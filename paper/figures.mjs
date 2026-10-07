// Generate the paper's meander figures as TikZ (for the LaTeX PDF) and SVG (for EPUB/HTML).
// Rivers come from an exact enumerator with the same crossing check and parity pruning as the
// verified search in Arnold/Defs.lean. Usage: node paper/figures.mjs
import { mkdirSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'

const outDir = join(dirname(fileURLToPath(import.meta.url)), 'figs')
mkdirSync(outDir, { recursive: true })

// Bridges 0..n-1 west to east; E = n (east end), S = n+1 (south end). path[0] = S.
// Arc j joins path[j] and path[j+1]; even arcs below the road, odd arcs above.
function* allMeanders(n) {
  const path = new Int32Array(n + 2), used = new Uint8Array(n)
  path[0] = n + 1
  const crosses = (t) => {
    const a = path[t], b = path[t + 1], lo = Math.min(a, b), hi = Math.max(a, b)
    for (let j = t - 2; j >= 0; j -= 2) {
      const c = path[j], d = path[j + 1]
      if ((c > lo && c < hi) !== (d > lo && d < hi)) return true
    }
    return false
  }
  const parityOK = (t) => {
    const cur = path[t]
    for (let j = 0; j < t; j++) {
      const a = path[j], b = path[j + 1], lo = Math.min(a, b), hi = Math.max(a, b)
      let k = 0
      for (let y = lo + 1; y < hi && y < n; y++) if (!used[y]) k++
      const s = j & 1
      if ((t & 1) === s && cur > lo && cur < hi) k++
      if ((n & 1) === s && n > lo && n < hi) k++
      if (k & 1) return false
    }
    return true
  }
  function* rec(t) {
    if (t === n) { path[n + 1] = n; if (!crosses(n)) yield Array.from(path.subarray(1, n + 1)); return }
    for (let x = 0; x < n; x++) {
      if (used[x]) continue
      used[x] = 1; path[t + 1] = x
      if (!crosses(t) && parityOK(t + 1)) yield* rec(t + 1)
      used[x] = 0
    }
  }
  yield* rec(0)
}

// Shared geometry in "units" (cm in TikZ). Returns the arcs, the entry and the exit.
function shape(n, perm, sx) {
  let maxUp = 0, maxDn = 0
  const arcs = []
  for (let i = 1; i < n; i++) {
    const a = perm[i - 1] * sx, b = perm[i] * sx, r = Math.abs(b - a) / 2, up = (i & 1) === 1
    if (up) maxUp = Math.max(maxUp, r); else maxDn = Math.max(maxDn, r)
    arcs.push({ a, b, r, up })
  }
  const exitUp = (n & 1) === 1
  const xl = perm[n - 1] * sx
  const h = ((exitUp ? maxUp : maxDn) + 0.3) * (exitUp ? 1 : -1)
  return { arcs, x0: perm[0] * sx, xl, h, exitUp, right: (n - 1 + 0.6) * sx + 0.35, left: -0.6 * sx }
}

const f = (x) => x.toFixed(3)

function tikz(n, perm, sx = 0.55) {
  const s = shape(n, perm, sx)
  let p = `\\draw[river] (${f(s.x0)},-1.35) -- (${f(s.x0)},0)`
  for (const { a, b, r, up } of s.arcs) {
    const ltr = a < b
    const [s0, s1] = up ? (ltr ? [180, 0] : [0, 180]) : (ltr ? [180, 360] : [360, 180])
    p += ` arc (${s0}:${s1}:${f(r)})`
  }
  p += ` -- (${f(s.xl)},${f(s.h * 0.7)}) to[out=${s.exitUp ? 90 : -90},in=180] (${f(s.xl + 0.35)},${f(s.h)}) -- (${f(s.right)},${f(s.h)});`
  const lines = [
    '\\begin{tikzpicture}[baseline=0pt]',
    `\\fill[road] (${f(s.left)},-0.07) rectangle (${f(s.right)},0.07);`,
    p,
    ...perm.map((_, i) => `\\fill[bridge] (${f(i * sx)},0) circle (0.055);`),
    '\\end{tikzpicture}',
  ]
  return lines.join('\n')
}

function svg(n, perm, sx = 0.55) {
  const s = shape(n, perm, sx), k = 100 // svg units per cm
  const X = (x) => f(x * k), Y = (y) => f(-y * k)
  const top = Math.max(1.35, s.exitUp ? s.h : 0, ...s.arcs.filter((a) => a.up).map((a) => a.r)) + 0.15
  const bot = Math.max(1.35, s.exitUp ? 0 : -s.h, ...s.arcs.filter((a) => !a.up).map((a) => a.r)) + 0.05
  let d = `M ${X(s.x0)} ${Y(-1.35)} L ${X(s.x0)} ${Y(0)}`
  for (const { a, b, r, up } of s.arcs) {
    const ltr = a < b
    const sweep = up ? (ltr ? 1 : 0) : (ltr ? 0 : 1)
    d += ` A ${X(r)} ${X(r)} 0 0 ${sweep} ${X(b)} ${Y(0)}`
  }
  const ex = s.xl, eh = s.h
  d += ` L ${X(ex)} ${Y(eh * 0.7)} C ${X(ex)} ${Y(eh)} ${X(ex + 0.1)} ${Y(eh)} ${X(ex + 0.35)} ${Y(eh)} L ${X(s.right)} ${Y(eh)}`
  const w = (s.right - s.left) * k, vb = `${f(s.left * k)} ${f(-top * k)} ${f(w)} ${f((top + bot) * k)}`
  const bridges = perm.map((_, i) => `<circle cx="${X(i * sx)}" cy="0" r="5.5" fill="#D98A1C"/>`).join('')
  return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="${vb}" width="${f(w * 0.6)}" height="${f((top + bot) * k * 0.6)}" role="img" aria-label="Open meander with ${n} crossings, crossing order ${perm.join('')}">` +
    `<rect x="${f(s.left * k)}" y="-7" width="${f(w)}" height="14" fill="#E6DCC5"/>` +
    `<path d="${d}" fill="none" stroke="#1E8F84" stroke-width="3.2" stroke-linecap="round" stroke-linejoin="round"/>` +
    bridges + '</svg>\n'
}

const write = (name, n, perm, sx) => {
  writeFileSync(join(outDir, `${name}.tex`), tikz(n, perm, sx) + '\n')
  writeFileSync(join(outDir, `${name}.svg`), svg(n, perm, sx))
}

const n4 = [...allMeanders(4)]
n4.forEach((p, i) => write(`n4-${i + 1}`, 4, p))
const n5 = [...allMeanders(5)]
n5.forEach((p, i) => write(`n5-${i + 1}`, 5, p, 0.6))
const n9 = [...allMeanders(9)][137]
write('n9-138', 9, n9, 0.62)

writeFileSync(join(outDir, 'orders.json'), JSON.stringify({ n4: n4.map((p) => p.join('')), n5: n5.map((p) => p.join('')), n9: n9.join('') }, null, 2) + '\n')
console.log(`n=4: ${n4.length}, n=5: ${n5.length}, n=9 example: ${n9.join('')}`)
