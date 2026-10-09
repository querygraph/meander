# Catalan numbers and the upper bound on meanders

Catalan's constant (G ≈ 0.91597) does not appear in this project. The upper bound uses the
**Catalan numbers** Cₙ, a different object despite the shared name.

## The bound

`Arnold/Catalan.lean` proves:

- `openMeanderCount_le_catalan_sq`: there are at most C₍ₙ₊₁₎² open meanders with 2n+1
  crossings.
- `closedMeanderCount_le_catalan_sq`: there are at most Cₙ² closed meanders of order n.

## Why Catalan numbers

Cut a meander along the road.

- The river's arcs above the road form a non-crossing matching of the crossing points, and so
  do the arcs below.
- Non-crossing matchings of 2n points correspond one-to-one to Dyck words of semilength n, and
  there are Cₙ of them.
- A meander is determined by its pair of matchings, so the map from meanders to pairs of Dyck
  words is injective. That gives the bound Cₙ².

Most pairs are not meanders: gluing two matchings usually gives several closed loops rather
than one river. So Cₙ² is only an upper bound.

## How loose it is

Cₙ grows like 4ⁿ / (n^{3/2} √π), so Cₙ² grows like 16ⁿ / (π n³). Against the computed values:

- C₂₈² = 69,562,982,052,510,226,587,760,129,600, about **6,500 times**
  A(55) = 10,726,008,363,361,842,734,385,644.
- The true growth per two extra crossings is A(56)/A(54) ≈ 10.88 and A(55)/A(53) ≈ 10.86,
  against the bound's 16.
- These ratios rise slowly from below toward the meander connective constant, about 12.26 per
  two crossings in the literature (about 3.50 per crossing), because of a polynomial
  correction factor. The bound allows 4 per crossing.

So the Catalan bound proves exponential growth with base at most 4 per crossing, while the
true base is about 3.5. No closed form for that constant is known, and estimating it is one
reason to compute terms like A(56).

Values: A(53), A(54), A(55) from OEIS A005316 (b-file n = 0..55, Andrew Howroyd) and
reproduced here; A(56) = 28,235,899,288,344,793,178,333,732 computed here by meet in the
middle and confirmed by a second split.
