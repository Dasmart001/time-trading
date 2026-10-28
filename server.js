'use strict';
/* Time Trading market server (reference implementation, no dependencies).
   Run:  node server.js            (test credits mode, serves the app at http://localhost:3000)
         TT_MODE=live node server.js   (balances start at 0; on-chain deposits must be wired in before real use)
   Data is kept in memory and saved to data.json every second. This is a development server:
   before real money, add TLS, a real database, wallet-signature login and a security review. */
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const PORT = +process.env.PORT || 3000, LIVE = process.env.TT_MODE === 'live';
const DATA = process.env.TT_DATA || path.join(__dirname, 'data.json');
const HR = 36e5, DAY = 864e5, FEE = 0.0025, BURN = 0.3, START = 1000, BUYCAP = 4;
const DEPR = [0.25, 0.2, 0.1], PCAP = [1, 2, 4];
let skew = 0; const now = () => Date.now() + skew;
let S = { users: {}, tokens: {}, handles: {}, slots: {}, orders: {}, units: {}, ledger: {}, receipts: [], id: 1, burned: 0, treasury: 0, vol: 0, trades: 0, secret: crypto.randomBytes(16).toString('hex') };
try { S = Object.assign(S, JSON.parse(fs.readFileSync(DATA, 'utf8'))); } catch (e) {}
let dirty = false; const mark = () => { dirty = true; };
setInterval(() => { if (dirty) { dirty = false; try { fs.writeFileSync(DATA, JSON.stringify(S)); } catch (e) {} } }, 1000);

const E = (code, msg) => Object.assign(new Error(msg), { code });
const R = n => Math.round(n * 1e6) / 1e6;
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const hmac = s => crypto.createHmac('sha256', S.secret).update(s).digest('hex');
const lvl = u => u.deliv >= 8 ? 2 : u.deliv >= 3 ? 1 : 0;
function lg(u, d, n) { const a = S.ledger[u.id] = S.ledger[u.id] || []; a.unshift({ t: now(), d: R(d), n }); a.length = Math.min(a.length, 100); }
function pay(u, d, n) { u.bal = R(u.bal + d); lg(u, d, n); mark(); }
const slot = t => S.slots[t] || (S.slots[t] = { t, bids: [], asks: [], trades: [], started: false });
const ord = (s, side) => (side === 'buy' ? s.bids : s.asks).map(id => S.orders[id]).filter(Boolean);
const unitsOf = (u, t, role) => Object.values(S.units).filter(x => x.t === t && x.status === 'held' && x[role] === u.id);
const openQty = (u, s, side, kind) => ord(s, side).filter(o => o.user === u.id && (!kind || o.kind === kind)).reduce((a, o) => a + o.rem, 0);
const bestAsk = (s, u) => ord(s, 'sell').filter(o => o.user !== u.id && o.rem > 0).sort((a, b) => a.price - b.price || a.ts - b.ts)[0];
const bestBid = (s, u) => ord(s, 'buy').filter(o => o.user !== u.id && o.rem > 0).sort((a, b) => b.price - a.price || a.ts - b.ts)[0];
const label = t => new Date(t).toISOString().slice(0, 16).replace('T', ' ') + ' UTC';

function drop(o) { const s = slot(o.t), k = o.side === 'buy' ? 'bids' : 'asks'; s[k] = s[k].filter(id => id !== o.id); delete S.orders[o.id]; mark(); }
function cancelOrder(o, why) {
  const u = S.users[o.user];
  if (o.rem > 0) {
    if (o.side === 'buy') pay(u, o.res * o.rem, why || 'Bid cancelled, funds returned');
    else if (o.kind === 'provide') pay(u, o.dep * o.rem, why || 'Offer cancelled, deposit returned');
    else o.units.forEach(id => { if (S.units[id]) S.units[id].listed = null; });
  }
  drop(o);
}
function execute(buyer, bid, ask, price, n) {
  const seller = S.users[ask.user], s = slot(ask.t), cost = price * n, fee = cost * FEE;
  if (bid) { bid.rem -= n; if (bid.rem <= 0) drop(bid); }
  else pay(buyer, -(cost + fee), 'Bought ' + n + ' h, ' + label(ask.t));
  S.burned = R(S.burned + fee * BURN); S.treasury = R(S.treasury + fee * (1 - BURN)); S.vol += n; S.trades++;
  if (ask.kind === 'provide') {
    for (let i = 0; i < n; i++) { const id = 'n' + S.id++; S.units[id] = { id, t: ask.t, provider: ask.user, holder: buyer.id, escrow: price, dep: ask.dep, status: 'held', hH: 0, hP: 0, listed: null }; }
  } else {
    const ids = ask.units.splice(0, n);
    ids.forEach(id => { const x = S.units[id]; x.holder = buyer.id; x.listed = null; });
    pay(seller, cost, 'Sold ' + n + ' h, ' + label(ask.t));
  }
  ask.rem -= n; if (ask.rem <= 0 && S.orders[ask.id]) drop(ask);
  s.trades.push({ ts: now(), p: price, q: n }); mark();
}
function place(u, b) {
  const t = +b.t, side = b.side, q = Math.floor(+b.qty);
  if (!Number.isFinite(t) || t % HR !== 0 || t <= now() || t > now() + 7 * DAY) throw E(400, 'That hour is not open for trading.');
  if (side !== 'buy' && side !== 'sell') throw E(400, 'Choose buy or sell.');
  if (!(q >= 1 && q <= BUYCAP)) throw E(400, 'Choose 1 to 4 hours.');
  const s = slot(t); if (s.started) throw E(400, 'That hour has started.');
  const limit = b.price === '' || b.price == null ? null : +b.price;
  if (limit !== null && !(limit > 0 && limit < 1e6)) throw E(400, 'Enter a valid price.');
  let filled = 0, resting = 0;
  if (side === 'buy') {
    if (unitsOf(u, t, 'holder').length + openQty(u, s, 'buy') + q > BUYCAP) throw E(400, 'Limit: 4 hours per hour-slot.');
    let rem = q;
    while (rem > 0) {
      const ask = bestAsk(s, u); if (!ask || (limit !== null && ask.price > limit)) break;
      let n = Math.min(rem, ask.rem); const per = ask.price * (1 + FEE), afford = Math.floor(u.bal / per + 1e-9);
      if (afford < 1) { if (!filled) throw E(400, 'Not enough $CLOCK.'); break; }
      n = Math.min(n, afford); execute(u, null, ask, ask.price, n); rem -= n; filled += n;
    }
    if (rem > 0 && limit === null && !filled) throw E(400, 'No offers right now. Set a price to place a bid.');
    if (rem > 0 && limit !== null) {
      const res = limit * (1 + FEE); rem = Math.min(rem, Math.floor(u.bal / res + 1e-9));
      if (rem < 1 && !filled) throw E(400, 'Not enough $CLOCK.');
      if (rem >= 1) {
        const o = { id: 'o' + S.id++, user: u.id, t, side: 'buy', kind: 'buy', qty: rem, rem, price: limit, res, ts: now() };
        pay(u, -res * rem, 'Bid held, ' + label(t)); S.orders[o.id] = o; s.bids.push(o.id); resting = rem; mark();
      }
    }
    return { filled, resting };
  }
  if (limit === null) throw E(400, 'Enter your price.');
  const kind = b.kind === 'provide' ? 'provide' : 'resell';
  const o = { id: 'o' + S.id++, user: u.id, t, side: 'sell', kind, qty: q, rem: q, price: limit, ts: now() };
  if (kind === 'provide') {
    const L = lvl(u), cap = PCAP[L], have = unitsOf(u, t, 'provider').length + openQty(u, s, 'sell', 'provide');
    if (have + q > cap) throw E(400, 'You can offer up to ' + cap + ' h per hour for now. Deliver hours to raise this.');
    o.dep = limit * DEPR[L]; if (u.bal < o.dep * q - 1e-9) throw E(400, 'Not enough $CLOCK for the deposit.');
    pay(u, -o.dep * q, 'Deposit held for an offer, ' + label(t));
  } else {
    const mine = unitsOf(u, t, 'holder').filter(x => !x.listed);
    if (mine.length < q) throw E(400, 'You do not hold that many hours here.');
    o.units = mine.slice(0, q).map(x => x.id); mine.slice(0, q).forEach(x => { x.listed = o.id; });
  }
  S.orders[o.id] = o;
  while (o.rem > 0) {
    const bid = bestBid(s, u); if (!bid || bid.price < limit) break;
    const n = Math.min(o.rem, bid.rem); execute(S.users[bid.user], bid, o, bid.price, n); filled += n;
  }
  if (o.rem > 0) { s.asks.push(o.id); resting = o.rem; } else delete S.orders[o.id];
  mark(); return { filled, resting };
}
function checkin(u, id) {
  const x = S.units[id]; if (!x || x.status !== 'held') throw E(404, 'Session not found.');
  if (now() < x.t || now() >= x.t + HR) throw E(400, 'Check-in is open only during the hour.');
  if (x.holder === u.id) x.hH = now(); else if (x.provider === u.id) x.hP = now(); else throw E(403, 'Not your session.');
  mark();
}
const body = r => JSON.stringify([r.n, r.unit, r.t, r.provider, r.holder, r.out, r.hH, r.hP, r.at, r.prev]);
function receipt(x, out, prov, hold) {
  const prev = S.receipts.length ? S.receipts[S.receipts.length - 1].h : 'genesis';
  const r = { n: S.receipts.length + 1, unit: x.id, t: x.t, provider: prov.handle, holder: hold.handle, out, hH: x.hH, hP: x.hP, at: now(), prev };
  r.h = sha(body(r)); r.sig = hmac(r.h); S.receipts.push(r);
}
function resolve(x) {
  const prov = S.users[x.provider], hold = S.users[x.holder], hh = !!x.hH, pp = !!x.hP; let out;
  if (hh && pp) { out = 'complete'; pay(prov, x.escrow + x.dep, 'Delivered: paid and deposit returned'); prov.deliv++; hold.att++; }
  else if (pp) { out = 'buyer no-show'; pay(prov, x.escrow + x.dep, 'Buyer did not show: paid and deposit returned'); prov.deliv++; hold.miss++; }
  else if (hh) { out = 'provider no-show'; pay(hold, x.escrow + x.dep, 'Provider did not show: refund plus bonus'); prov.slash++; }
  else { out = 'void'; pay(hold, x.escrow, 'No one checked in: refunded'); pay(prov, x.dep, 'No one checked in: deposit returned'); }
  x.status = 'done'; x.out = out; receipt(x, out, prov, hold); mark();
}
function tick() {
  const n = now();
  for (const s of Object.values(S.slots)) {
    if (!s.started && n >= s.t) { s.started = true; [...s.bids, ...s.asks].forEach(id => { const o = S.orders[id]; if (o) cancelOrder(o, 'Hour started: order cancelled and returned'); }); }
    if (s.t < n - 14 * DAY) delete S.slots[s.t];
  }
  Object.values(S.units).filter(x => x.status === 'held' && n >= x.t + HR).forEach(resolve);
}
setInterval(tick, 1000);

function pubUnit(x, me) {
  const o = id => (S.users[id] || {}).handle;
  return { id: x.id, t: x.t, role: x.holder === me.id ? 'holder' : 'provider', escrow: x.escrow, dep: x.dep, hH: x.hH, hP: x.hP, status: x.status, out: x.out || null, listed: !!x.listed, holder: o(x.holder), provider: o(x.provider) };
}
function meView(u) {
  const units = Object.values(S.units).filter(x => (x.holder === u.id || x.provider === u.id) && (x.status === 'held' || now() - x.t < 6 * HR)).map(x => pubUnit(x, u));
  const orders = Object.values(S.orders).filter(o => o.user === u.id).map(o => ({ id: o.id, t: o.t, side: o.side, kind: o.kind, rem: o.rem, price: o.price }));
  return { user: { id: u.id, handle: u.handle, bal: u.bal, level: lvl(u) + 1, deliv: u.deliv, att: u.att, miss: u.miss, slash: u.slash }, units, orders, caps: { buy: BUYCAP, provide: PCAP[lvl(u)], dep: DEPR[lvl(u)] } };
}
function candles(s) {
  const out = {}, st = 3e5;
  for (const x of s.trades) { const k = Math.floor(x.ts / st) * st, c = out[k]; if (c) { c.h = Math.max(c.h, x.p); c.l = Math.min(c.l, x.p); c.c = x.p; c.v += x.q; } else out[k] = { k, o: x.p, h: x.p, l: x.p, c: x.p, v: x.q }; }
  return Object.values(out).sort((a, b) => a.k - b.k);
}
function usual(t) {
  const h = new Date(t).getUTCHours(); let v = 0, w = 0;
  for (const s of Object.values(S.slots)) if (s.t !== t && new Date(s.t).getUTCHours() === h) for (const x of s.trades) { v += x.p * x.q; w += x.q; }
  return w ? R(v / w) : null;
}
const levels = (list, desc) => { const m = {}; list.forEach(o => { m[o.price] = (m[o.price] || 0) + o.rem; }); return Object.keys(m).map(p => ({ p: +p, q: m[p] })).sort((a, b) => desc ? b.p - a.p : a.p - b.p).slice(0, 5); };
function slotView(t) {
  const s = S.slots[t] || { t, bids: [], asks: [], trades: [] }, asks = ord(s, 'sell'), bids = ord(s, 'buy');
  const last = s.trades.length ? s.trades[s.trades.length - 1].p : null;
  return { t, last, ask: asks.length ? Math.min(...asks.map(o => o.price)) : null, bid: bids.length ? Math.max(...bids.map(o => o.price)) : null, asks: levels(asks, false), bids: levels(bids, true), candles: candles(s), usual: usual(t), vol: s.trades.reduce((a, x) => a + x.q, 0) };
}
function marketView() {
  const base = Math.floor(now() / HR) * HR, out = [];
  for (let t = base + HR; t <= base + 7 * DAY; t += HR) { const s = S.slots[t]; if (s && (s.trades.length || s.asks.length || s.bids.length)) { const v = slotView(t); out.push({ t, last: v.last, ask: v.ask, bid: v.bid, vol: v.vol }); } }
  return out;
}
function verify() {
  let prev = S.receipts.length ? S.receipts[0].prev : 'genesis';
  for (const r of S.receipts) { if (r.prev !== prev || sha(body(r)) !== r.h || hmac(r.h) !== r.sig) return { ok: false, brokenAt: r.n, n: S.receipts.length }; prev = r.h; }
  return { ok: true, n: S.receipts.length };
}

const hits = {};
setInterval(() => { for (const k in hits) delete hits[k]; }, 60000);
const routes = [
  ['GET', /^\/api\/config$/, false, () => ({ mode: LIVE ? 'live' : 'test', currency: '$CLOCK', fee: FEE, startBal: LIVE ? 0 : START })],
  ['POST', /^\/api\/join$/, false, (u, p, b) => {
    const h = String(b.handle || '').trim();
    if (!/^[A-Za-z0-9_.-]{2,20}$/.test(h)) throw E(400, 'Use 2 to 20 letters, numbers, dots or dashes.');
    if (S.handles[h.toLowerCase()]) throw E(409, 'That handle is taken.');
    const id = 'u' + S.id++, token = crypto.randomBytes(24).toString('hex');
    S.users[id] = { id, handle: h, bal: LIVE ? 0 : START, deliv: 0, att: 0, miss: 0, slash: 0, fct: 0, created: now() };
    S.tokens[token] = id; S.handles[h.toLowerCase()] = id;
    if (!LIVE) lg(S.users[id], START, 'Welcome credits (test mode)');
    mark(); return { token, user: S.users[id].handle };
  }],
  ['POST', /^\/api\/auth\/wallet$/, false, () => { throw E(501, 'Wallet login is not enabled yet.'); }],
  ['GET', /^\/api\/me$/, true, u => meView(u)],
  ['GET', /^\/api\/market$/, false, () => ({ slots: marketView() })],
  ['GET', /^\/api\/slot\/(\d+)$/, false, (u, p) => slotView(+p[1])],
  ['POST', /^\/api\/orders$/, true, (u, p, b) => place(u, b)],
  ['DELETE', /^\/api\/orders\/(\w+)$/, true, (u, p) => { const o = S.orders[p[1]]; if (!o || o.user !== u.id) throw E(404, 'Order not found.'); cancelOrder(o); return { ok: true }; }],
  ['POST', /^\/api\/checkin$/, true, (u, p, b) => { checkin(u, b.unit); return { ok: true }; }],
  ['GET', /^\/api\/ledger$/, true, u => ({ items: S.ledger[u.id] || [] })],
  ['GET', /^\/api\/receipts$/, true, u => ({ items: S.receipts.filter(r => r.provider === u.handle || r.holder === u.handle).slice(-30).reverse() })],
  ['GET', /^\/api\/verify$/, false, () => verify()],
  ['GET', /^\/api\/stats$/, false, () => ({ vol: S.vol, trades: S.trades, burned: S.burned, treasury: S.treasury, users: Object.keys(S.users).length })],
  ['POST', /^\/api\/faucet$/, true, u => { if (LIVE) throw E(403, 'Not available in live mode.'); if (now() - u.fct < 60000) throw E(429, 'Come back in a minute for more.'); u.fct = now(); pay(u, 100, 'Test credits'); return { ok: true }; }],
  ['POST', /^\/api\/_skip$/, false, (u, p, b) => { if (LIVE) throw E(403, 'Not available in live mode.'); skew += Math.min(+b.ms || 18e5, 6 * HR); tick(); return { ok: true }; }]
];
const server = http.createServer((req, res) => {
  const cors = { 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type, Authorization', 'Access-Control-Allow-Methods': 'GET,POST,DELETE,OPTIONS' };
  if (req.method === 'OPTIONS') { res.writeHead(204, cors); return res.end(); }
  const url = new URL(req.url, 'http://x'), send = (code, obj) => { res.writeHead(code, Object.assign({ 'Content-Type': 'application/json' }, cors)); res.end(JSON.stringify(Object.assign({ now: now() }, obj))); };
  if (!url.pathname.startsWith('/api/')) {
    if (url.pathname === '/' || url.pathname === '/index.html') { try { res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' }); return res.end(fs.readFileSync(path.join(__dirname, 'time-trading.html'))); } catch (e) { res.writeHead(404); return res.end('time-trading.html not found next to server.js'); } }
    res.writeHead(404); return res.end('Not found');
  }
  const ip = req.socket.remoteAddress; hits[ip] = (hits[ip] || 0) + 1; if (hits[ip] > 600) return send(429, { error: 'Too many requests.' });
  let raw = ''; req.on('data', c => { raw += c; if (raw.length > 1e4) req.destroy(); });
  req.on('end', () => {
    try {
      const body = raw ? JSON.parse(raw) : {}, tok = (req.headers.authorization || '').replace('Bearer ', ''), user = S.users[S.tokens[tok]];
      for (const [m, re, auth, fn] of routes) {
        const p = url.pathname.match(re); if (m !== req.method || !p) continue;
        if (auth && !user) return send(401, { error: 'Please sign in.' });
        return send(200, fn(user, p, body) || {});
      }
      send(404, { error: 'Unknown request.' });
    } catch (e) { send(e.code || 500, { error: e.code ? e.message : 'Something went wrong.' }); if (!e.code) console.error(e); }
  });
});
server.listen(PORT, () => console.log('Time Trading market on http://localhost:' + PORT + (LIVE ? ' (LIVE mode)' : ' (test credits mode)')));
