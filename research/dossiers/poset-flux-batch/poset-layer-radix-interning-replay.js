function replay() {
  let seed = 238181;
  const rand = () => ((seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0) / 4294967296);
  const stats = { cases: 0, states: 0, arcs: 0, pairChecks: 0 };
  function countingSort(records, key, range) {
    const offsets = Array(range).fill(0);
    for (const record of records) offsets[record[key]]++;
    let total = 0;
    for (let i = 0; i < range; i++) {
      const count = offsets[i];
      offsets[i] = total;
      total += count;
    }
    const result = Array(records.length);
    for (const record of records) result[offsets[record[key]]++] = record;
    return result;
  }
  function check(n, pred, chains) {
    const w = chains.length;
    const bit = i => 1 << i;
    const req = pred.map(mask => chains.map(chain =>
      chain.reduce((last, x, i) => mask & bit(x) ? i + 1 : last, 0)));
    function deficit(v, p) {
      if (v === undefined) return -1;
      return req[v].reduce((sum, need, c) => sum + (p[c] < need), 0);
    }
    function intern(lo, hi, layer, updates) {
      if (hi - lo === 1) {
        const base = layer.map(state => state.p[lo]);
        for (const update of updates) update.id = base[update.parent] + 1;
        return { base, range: chains[lo].length + 1 };
      }
      const mid = (lo + hi) >> 1;
      const leftUpdates = [], rightUpdates = [];
      for (const update of updates)
        (update.c < mid ? leftUpdates : rightUpdates).push(update);
      const left = intern(lo, mid, layer, leftUpdates);
      const right = intern(mid, hi, layer, rightUpdates);
      const records = layer.map((_, index) => ({ l: left.base[index], r: right.base[index], index }));
      for (const update of updates) records.push({
        l: update.c < mid ? update.id : left.base[update.parent],
        r: update.c >= mid ? update.id : right.base[update.parent],
        update
      });
      const sorted = countingSort(countingSort(records, "r", right.range), "l", left.range);
      const base = Array(layer.length);
      let lastL = -1, lastR = -1, id = -1;
      for (const record of sorted) {
        if (record.l !== lastL || record.r !== lastR) {
          id++;
          lastL = record.l;
          lastR = record.r;
        }
        if (record.update) record.update.id = id;
        else base[record.index] = id;
      }
      return { base, range: id + 1 };
    }
    const zero = Array(w).fill(0);
    let layer = [{ p: zero, d: chains.map(chain => deficit(chain[0], zero)), mask: 0, arcs: [], f: 1n, b: 0n }];
    const states = layer.slice();
    for (let k = 0; k < n; k++) {
      const updates = [];
      for (let parent = 0; parent < layer.length; parent++) {
        for (let c = 0; c < w; c++)
          if (layer[parent].d[c] === 0) updates.push({ parent, c });
      }
      const { range } = intern(0, w, layer, updates);
      const byId = Array(range);
      const next = [];
      for (const { parent, c, id } of updates) {
        const from = layer[parent], y = chains[c][from.p[c]], mask = from.mask | bit(y);
        let to = byId[id];
        if (!to) {
          const p = from.p.slice();
          p[c]++;
          const d = from.d.map((old, j) => {
            const v = chains[j][p[j]];
            if (j === c) return deficit(v, p);
            return v === undefined ? -1 : old - (req[v][c] === p[c]);
          });
          if (d.some((value, j) => value !== deficit(chains[j][p[j]], p))) throw Error("deficit");
          to = { p, d, mask, arcs: [], f: 0n, b: 0n };
          byId[id] = to;
          next.push(to);
        }
        if (to.mask !== mask) throw Error("coalesced unequal vectors");
        from.arcs.push({ y, to });
        to.f += from.f;
        stats.arcs++;
      }
      states.push(...next);
      layer = next;
    }
    const seen = new Set(states.map(state => state.mask));
    if (seen.size !== states.length) throw Error("duplicate");
    for (let mask = 0; mask < bit(n); mask++) {
      const ideal = pred.every((need, x) => !(mask & bit(x)) || (need & mask) === need);
      if (seen.has(mask) !== ideal) throw Error("ideal coverage");
      if (ideal) {
        const state = states.find(entry => entry.mask === mask);
        for (let y = 0; y < n; y++) {
          const addable = !(mask & bit(y)) && (pred[y] & mask) === pred[y];
          if (state.arcs.filter(arc => arc.y === y).length !== Number(addable)) throw Error("arcs");
        }
      }
    }
    layer[0].b = 1n;
    for (let i = states.length - 2; i >= 0; i--)
      for (const { to } of states[i].arcs) states[i].b += to.b;
    const offsets = [];
    let cells = 0;
    for (const chain of chains) {
      offsets.push(cells);
      cells += chain.length + 1;
    }
    const diff = Array.from({ length: n }, () => Array(cells).fill(0n));
    const direct = Array.from({ length: n }, () => Array(n).fill(0n));
    for (let start = 0; start < states.length; start += n) {
      const block = states.slice(start, start + n);
      const a = Array.from({ length: n }, () => Array(block.length).fill(0n));
      const g = block.map(state => {
        const row = Array(cells).fill(0n);
        for (let c = 0; c < w; c++) {
          row[offsets[c]]++;
          row[offsets[c] + state.p[c]]--;
        }
        return row;
      });
      block.forEach((state, i) => {
        for (const { y, to } of state.arcs) a[y][i] = state.f * to.b;
      });
      const h = block.map(state => Array.from({ length: n }, (_, x) =>
        BigInt(Boolean(state.mask & bit(x)))));
      for (let y = 0; y < n; y++) {
        for (let i = 0; i < block.length; i++) {
          for (let u = 0; u < cells; u++) diff[y][u] += a[y][i] * g[i][u];
          for (let x = 0; x < n; x++) direct[y][x] += a[y][i] * h[i][x];
        }
      }
    }
    const expected = Array.from({ length: n }, () => Array(n).fill(0n));
    let extensionCount = 0n;
    function visit(mask, order) {
      if (order.length === n) {
        extensionCount++;
        for (let j = 0; j < n; j++)
          for (let i = 0; i < j; i++) expected[order[j]][order[i]]++;
        return;
      }
      for (let y = 0; y < n; y++) {
        if (!(mask & bit(y)) && (pred[y] & mask) === pred[y]) {
          order.push(y);
          visit(mask | bit(y), order);
          order.pop();
        }
      }
    }
    visit(0, []);
    if (extensionCount !== states[0].b || extensionCount !== layer[0].f) throw Error("total");
    for (let y = 0; y < n; y++) {
      for (let c = 0; c < w; c++) {
        let count = 0n;
        for (let i = 0; i < chains[c].length; i++) {
          count += diff[y][offsets[c] + i];
          const x = chains[c][i];
          if (count !== expected[y][x] || direct[y][x] !== expected[y][x]) throw Error("pair count");
          stats.pairChecks++;
        }
        if (count + diff[y][offsets[c] + chains[c].length] !== 0n) throw Error("sentinel");
      }
    }
    stats.cases++;
    stats.states += states.length;
  }
  for (let t = 0; t < 900; t++) {
    const n = 1 + Math.floor(rand() * 8);
    const p = t % 19 === 0 ? 0 : t % 23 === 0 ? 1 : 0.1 + rand() * 0.7;
    const pred = Array(n).fill(0);
    for (let j = 0; j < n; j++) {
      for (let i = 0; i < j; i++) if (rand() < p) pred[j] |= (1 << i) | pred[i];
    }
    const chains = [];
    for (let i = 0; i < n; i++) {
      const eligible = chains.filter(chain => pred[i] & (1 << chain[chain.length - 1]));
      if (eligible.length && rand() > 0.25) eligible[Math.floor(rand() * eligible.length)].push(i);
      else chains.push([i]);
    }
    check(n, pred, chains);
  }
  return stats;
}
console.log(replay());
