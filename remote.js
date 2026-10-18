'use strict';
/* שקט v0.12 — remote control plumbing: crypto, pairing, rooms and transports. Knows nothing about audio or the UI;
   app.js (section "remote control") owns the state model and decides what to send / apply.

   Security model
   - Room secret: 128 random bits, generated on the PLAYER, stored in localStorage on both phones after pairing.
   - Every message is AES-GCM-256 encrypted with a key HKDF-derived from the secret (info "msg"); the relay topic is
     a separate HKDF output (info "topic"), so the relay sees only an opaque topic id + ciphertext, never the secret.
   - Pairing: the player shows a 6-digit code. The code is never the secret — it only names a short-lived (5 min),
     single-use mailbox: lookup id = HKDF(code) and mailbox content = the secret wrapped with AES-GCM under
     PBKDF2(code, 200k). The controller enters the code, fetches + unwraps the secret, then both talk on the room.
     A 6-digit code is brute-forceable OFFLINE by whoever holds the mailbox blob (the relay), so the TTL + single use
     + the player seeing "connected" are the real protection; a PAKE (CPace/SPAKE2) would close that gap later.

   Transport interface (what any relay must provide; Room/pairing pass only derived ids + ciphertext):
     announce(id, blob, ttlMs) -> Promise      put a pairing mailbox (id = derived from the code, blob = wrapped secret)
     withdraw(id)              -> Promise      remove it (single use / expired / new code)
     lookup(id)                -> Promise<blob|null>  fetch (and consume) a mailbox
     publish(topic, data)      -> Promise      data = base64url ciphertext string
     subscribe(topic, cb)      -> unsubscribe fn; cb(data) for every message on the topic (own messages may echo)
     ready (bool), name (string)                                                                                 */
(() => {
  const te = new TextEncoder(), td = new TextDecoder();
  const SALT = te.encode('shaket-rc/v1');
  const b64u = (u8) => btoa(String.fromCharCode(...u8)).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  const unb64u = (s) => Uint8Array.from(atob(s.replace(/-/g, '+').replace(/_/g, '/')), (c) => c.charCodeAt(0));
  const hex = (u8) => Array.from(u8, (b) => b.toString(16).padStart(2, '0')).join('');
  const rand = (n) => crypto.getRandomValues(new Uint8Array(n));
  const subtle = () => {
    if (!window.crypto || !crypto.subtle) throw new Error('webcrypto unavailable (needs https or localhost)');
    return crypto.subtle;
  };

  function newSecret() { return b64u(rand(16)); } // 128 bits
  function newId() { return b64u(rand(9)); }
  function newCode() { // uniform 6 digits (rejection sampling, no modulo bias)
    const a = new Uint32Array(1), lim = Math.floor(0x100000000 / 1e6) * 1e6;
    do crypto.getRandomValues(a); while (a[0] >= lim);
    return String(a[0] % 1e6).padStart(6, '0');
  }
  async function hkdfBits(ikm, info, bits) {
    const k = await subtle().importKey('raw', ikm, 'HKDF', false, ['deriveBits']);
    return new Uint8Array(await subtle().deriveBits({ name: 'HKDF', hash: 'SHA-256', salt: SALT, info: te.encode(info) }, k, bits));
  }
  async function hkdfKey(ikm, info) {
    const k = await subtle().importKey('raw', ikm, 'HKDF', false, ['deriveKey']);
    return subtle().deriveKey({ name: 'HKDF', hash: 'SHA-256', salt: SALT, info: te.encode(info) }, k,
      { name: 'AES-GCM', length: 256 }, false, ['encrypt', 'decrypt']);
  }
  async function seal(key, bytes, aad) {
    const iv = rand(12);
    const ct = new Uint8Array(await subtle().encrypt({ name: 'AES-GCM', iv, additionalData: te.encode(aad) }, key, bytes));
    const out = new Uint8Array(12 + ct.length); out.set(iv); out.set(ct, 12);
    return b64u(out);
  }
  async function unseal(key, str, aad) {
    const all = unb64u(str);
    return new Uint8Array(await subtle().decrypt({ name: 'AES-GCM', iv: all.slice(0, 12), additionalData: te.encode(aad) }, key, all.slice(12)));
  }

  // ---------- pairing (code -> long secret) ----------
  const codeOk = (c) => /^\d{6}$/.test(c);
  async function pairId(code) { return hex(await hkdfBits(te.encode('pair:' + code), 'pair-id', 128)); }
  async function pairKey(code) {
    const k = await subtle().importKey('raw', te.encode(code), 'PBKDF2', false, ['deriveKey']);
    return subtle().deriveKey({ name: 'PBKDF2', hash: 'SHA-256', salt: te.encode('shaket-rc/v1/pair'), iterations: 200000 }, k,
      { name: 'AES-GCM', length: 256 }, false, ['encrypt', 'decrypt']);
  }
  // player: put the wrapped secret in a mailbox named by the code; returns { code, id, exp }
  async function offer(transport, secret, ttlMs) {
    const code = newCode(), id = await pairId(code);
    const blob = await seal(await pairKey(code), te.encode(secret), 'pair');
    await transport.announce(id, blob, ttlMs);
    return { code, id, exp: Date.now() + ttlMs };
  }
  // controller: code -> secret (null = no such / expired / already used code)
  async function claim(transport, code) {
    if (!codeOk(code)) return null;
    const blob = await transport.lookup(await pairId(code));
    if (!blob) return null;
    try { return td.decode(await unseal(await pairKey(code), blob, 'pair')); } catch (e) { return null; }
  }

  // ---------- room: an encrypted, replay-checked message channel over any transport ----------
  // Envelope (plaintext, before encryption): { v:1, type:'state'|'cmd'|'hello'|'ack', from, boot, ts, seq, ...body }
  class Room {
    constructor({ transport, secret, deviceId, onMessage, onChange }) {
      Object.assign(this, { transport, secret, deviceId, onMessage, onChange });
      this.rx = Promise.resolve(); this.tx = Promise.resolve();
      this.boot = newId(); this.seq = 0; this.key = null; this.topic = null; this.unsub = null; this.hb = 0;
      this.peers = {}; // from -> { boot, seq, ts, seen }
      this.lastSeen = 0; this.open = false;
      this.counts = { sent: 0, recv: 0, dropped: 0, byType: {} };
    }
    async start(helloBody) {
      const ikm = unb64u(this.secret);
      this.key = await hkdfKey(ikm, 'msg');
      this.topic = hex(await hkdfBits(ikm, 'topic', 128));
      // serialized: decrypting is async, and a message overtaking an older one would make that one look like a replay
      this.unsub = this.transport.subscribe(this.topic, (d) => { this.rx = this.rx.then(() => this.receive(d)); });
      this.open = true;
      this.helloBody = helloBody || {};
      this.hb = setInterval(() => { this.send('hello', Object.assign({ hb: 1 }, this.helloBody)); }, Room.HEARTBEAT_MS);
      this.changed();
    }
    stop() {
      this.open = false;
      clearInterval(this.hb); this.hb = 0;
      if (this.unsub) { try { this.unsub(); } catch (e) { /* noop */ } this.unsub = null; }
      this.changed();
    }
    changed() { if (this.onChange) try { this.onChange(this); } catch (e) { console.error(e); } }
    // returns the message's seq synchronously-assigned (sends are serialized so seq order = wire order)
    send(type, body) {
      if (!this.open) return 0;
      const msg = Object.assign({}, body, { v: 1, type, from: this.deviceId, boot: this.boot, ts: Date.now(), seq: ++this.seq });
      this.tx = this.tx.then(async () => {
        await this.transport.publish(this.topic, await seal(this.key, te.encode(JSON.stringify(msg)), this.topic));
        this.counts.sent++; this.counts.byType[type] = (this.counts.byType[type] || 0) + 1;
      }).catch(() => { this.counts.failed = (this.counts.failed || 0) + 1; });
      return msg.seq;
    }
    async receive(data) {
      let msg;
      try { msg = JSON.parse(td.decode(await unseal(this.key, data, this.topic))); } catch (e) { this.counts.dropped++; return; } // not ours / tampered
      if (!msg || msg.v !== 1 || typeof msg.from !== 'string' || msg.from === this.deviceId) return; // own echo
      const p = this.peers[msg.from];
      if (p && p.boot === msg.boot && msg.seq <= p.seq) { this.counts.dropped++; return; } // replay / duplicate
      if (p && p.boot !== msg.boot && msg.ts < p.ts) { this.counts.dropped++; return; } // a replayed older boot
      const now = Date.now();
      // clock offset estimate (their ts -> our clock): the smallest observed (now - ts) = offset + min latency
      const skew = p && p.skew != null ? Math.min(p.skew, now - msg.ts) : now - msg.ts;
      this.peers[msg.from] = { boot: msg.boot, seq: msg.seq, ts: msg.ts, seen: now, skew, role: msg.role || (p && p.role) };
      this.lastSeen = now; this.counts.recv++;
      if (this.onMessage) try { this.onMessage(msg, this.peers[msg.from]); } catch (e) { console.error(e); }
      this.changed();
    }
    status() {
      if (!this.open || !this.transport.ready) return 'disconnected';
      return Date.now() - this.lastSeen < Room.STALE_MS ? 'connected' : 'connecting';
    }
  }
  Room.HEARTBEAT_MS = 20000;
  Room.STALE_MS = 50000; // > 2 missed heartbeats

  // ---------- LocalTransport: BroadcastChannel (same origin, same browser) — tests / two tabs ----------
  class LocalTransport {
    constructor(name) {
      this.name = 'local'; this.ready = true;
      this.bc = new BroadcastChannel(name || 'shaket-rc-local');
      this.subs = new Map(); this.boxes = new Map(); this.waits = new Map();
      this.bc.onmessage = (e) => this.onmsg(e.data || {});
    }
    onmsg(m) {
      if (m.k === 'pub') { const s = this.subs.get(m.topic); if (s) s.forEach((cb) => cb(m.data)); }
      else if (m.k === 'lookup') {
        const b = this.boxes.get(m.id);
        if (b && b.exp > Date.now()) { this.boxes.delete(m.id); this.bc.postMessage({ k: 'found', rid: m.rid, blob: b.blob }); } // single use
      } else if (m.k === 'found') { const w = this.waits.get(m.rid); if (w) { this.waits.delete(m.rid); w(m.blob); } }
    }
    async announce(id, blob, ttlMs) { this.boxes.set(id, { blob, exp: Date.now() + ttlMs }); }
    async withdraw(id) { this.boxes.delete(id); }
    lookup(id, timeoutMs) {
      const rid = newId();
      return new Promise((res) => {
        this.waits.set(rid, res);
        setTimeout(() => { if (this.waits.delete(rid)) res(null); }, timeoutMs || 2500);
        this.bc.postMessage({ k: 'lookup', id, rid });
      });
    }
    async publish(topic, data) { this.bc.postMessage({ k: 'pub', topic, data }); }
    subscribe(topic, cb) {
      if (!this.subs.has(topic)) this.subs.set(topic, new Set());
      this.subs.get(topic).add(cb);
      return () => { const s = this.subs.get(topic); if (s) s.delete(cb); };
    }
  }

  // ---------- RelayTransport: NOT ACTIVE — the network relay is not approved yet ----------
  // Nothing here touches the network. app.js only constructs it when its RC_RELAY constant is set.
  class RelayTransport {
    constructor(cfg) { this.cfg = cfg || {}; this.name = 'relay:' + (this.cfg.kind || 'none'); this.ready = false; }
    // TODO(ntfy.sh): publish = fetch(`${base}/${topic}`, { method: 'POST', body: data }) (topic = the hex HKDF topic id,
    //   32 chars; a self-hosted ntfy or ntfy.sh with an access token; message size limit 4 KB is plenty).
    //   subscribe = new EventSource(`${base}/${topic}/sse`) (or the JSON stream `/json`), cb(JSON.parse(e.data).message);
    //   reconnect with backoff, `since=<last id>` to catch up after a drop; set ready = true while the stream is open.
    //   announce/lookup: ntfy has no delete — use a second topic `pair-<id>` with a cached message (`Cache: yes`,
    //   ttl via the server's cache duration) read once with `/json?poll=1&since=5m`; single use is then enforced by the
    //   player (it rotates the code after the first hello) rather than by the relay.
    // TODO(Firebase RTDB): rooms/<topic>/msgs push() + onChildAdded (limitToLast(20)), pair/<id> = {blob, exp} written
    //   by the player and read+removed in a transaction by the controller; security rules allow only these paths, with
    //   value size limits and exp checks; anonymous auth. Messages stay ciphertext either way.
    async announce() { throw new Error('relay not enabled'); }
    async withdraw() { throw new Error('relay not enabled'); }
    async lookup() { throw new Error('relay not enabled'); }
    async publish() { throw new Error('relay not enabled'); }
    subscribe() { return () => {}; }
  }

  window.ShaketRemote = { Room, LocalTransport, RelayTransport, newSecret, newId, newCode, offer, claim, codeOk };
})();
