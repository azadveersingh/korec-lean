import Mathlib

/-!
# Collatz: basic definitions

The conjecture is only *stated* here, as a `Prop`. It is not proven.
-/

namespace Collatz

/-- The Collatz map `C(n) = n / 2` if `n` is even, `3n + 1` otherwise. -/
def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` reaches `1` after finitely many applications of `step`. -/
def ReachesOne (n : ℕ) : Prop := ∃ k, step^[k] n = 1

/-- The Collatz conjecture. Stated, **not proven**. -/
def Conjecture : Prop := ∀ n, 0 < n → ReachesOne n

end Collatz
