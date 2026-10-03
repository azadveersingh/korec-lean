# A short formal proof of Korec's density theorem for the 3x+1 map

This repository contains the Lean 4 code for the paper

> Azad and Shastri L. Nimmagadda, _A short formal proof of Korec's density theorem for the 3x+1 map_, 2026.

Let T be the shortcut Collatz map, T(n) = n/2 for even n and T(n) = (3n+1)/2 for odd n.
Korec (1994) proved that for every real θ > log₄ 3 ≈ 0.7925, the set of n with T^k(n) < n^θ for some k
has natural density one. The main theorem is `Collatz.korec_density_one` in `formal/Collatz/Korec.lean`.

## Files

| File                           | Lines | Content                                           |
| ------------------------------ | ----- | ------------------------------------------------- |
| `formal/Collatz/Basic.lean`    | 20    | imports; the 3x+1 map (not used in the proof)     |
| `formal/Collatz/Residues.lean` | 125   | T, e_L, affine formula, residue certificates      |
| `formal/Collatz/Korec.lean`    | 353   | the density theorem, the power saving, and lemmas |

## Build

Lean `v4.34.1` and Mathlib `v4.34.1` (commit `d13f23b`), fixed by `lean-toolchain` and `lake-manifest.json`.

```
cd formal
lake exe cache get
lake build Collatz.Korec
```

To check the axioms, run `#print axioms Collatz.korec_density_one` in a file that imports `Collatz`.
It reports only `propext`, `Classical.choice` and `Quot.sound`. The code contains no `sorry`.

The version described in the paper is the tag `v1`.

## Licence

Apache-2.0. See `LICENSE`.
