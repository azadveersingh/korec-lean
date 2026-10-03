import Collatz.Basic

/-!
# Residue classes mod 2^k (Terras)

For the shortcut map `T`, the first `k` parities of the orbit of `r + 2^k * m` do not depend on `m`,
and for `i ≤ k`

    T^[i] (r + 2^k * m) = 3^(oddCount r i) * 2^(k - i) * m + T^[i] r.

Consequently, if `3^(oddCount r i) < 2^i` ("the class is certified at step `i`"), then every
large enough `n ≡ r (mod 2^k)` drops below itself within `i` steps.
-/

namespace Collatz

/-- The shortcut map `T(n) = n / 2` (even), `(3n + 1) / 2` (odd). -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Number of odd values among `n, T n, …, T^[i-1] n`. -/
def oddCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => oddCount n i + T^[i] n % 2

/-- Adding an even number `2a` does not change the parity, so `T` acts affinely. -/
theorem T_two_mul_add (a x : ℕ) :
    T (2 * a + x) = 3 ^ (x % 2) * a + T x := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · rw [h, pow_zero, one_mul]; unfold T; split_ifs <;> omega
  · rw [h, pow_one]; unfold T; split_ifs <;> omega

/-- **Terras' affine formula.** -/
theorem T_iterate_affine (r m k : ℕ) :
    ∀ i, i ≤ k → T^[i] (r + 2 ^ k * m) = 3 ^ oddCount r i * 2 ^ (k - i) * m + T^[i] r := by
  intro i
  induction i with
  | zero => intro _; simp [oddCount, add_comm]
  | succ i ih =>
    intro hi
    obtain ⟨d, hd⟩ : ∃ d, k - i = d + 1 := ⟨k - i - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega),
      show k - (i + 1) = d by omega, hd, pow_succ,
      show 3 ^ oddCount r i * (2 ^ d * 2) * m = 2 * (3 ^ oddCount r i * 2 ^ d * m) by ring,
      T_two_mul_add, oddCount, pow_add]
    ring

/-- **Certified drop.** If `3^(oddCount r i) < 2^i` with `i ≤ k`, then `n = r + 2^k m` satisfies
`T^[i] n < n` as soon as `T^[i] r < m + r` (in particular for all large `m`). -/
theorem drop_of_certified {r m k i : ℕ} (hi : i ≤ k)
    (hc : 3 ^ oddCount r i < 2 ^ i) (hm : T^[i] r < m + r) :
    T^[i] (r + 2 ^ k * m) < r + 2 ^ k * m := by
  rw [T_iterate_affine r m k i hi]
  have hk : 2 ^ i * 2 ^ (k - i) = 2 ^ k := by rw [← pow_add, Nat.add_sub_cancel' hi]
  have hB : 1 ≤ 2 ^ (k - i) := Nat.one_le_two_pow
  have hAB : (3 ^ oddCount r i + 1) * 2 ^ (k - i) ≤ 2 ^ k :=
    hk ▸ Nat.mul_le_mul_right _ hc
  nlinarith [Nat.mul_le_mul_right m hAB, Nat.mul_le_mul_right m hB]

/-! ## Computable certificates -/

/-- The first step `i ∈ [1, k]` at which the class `r mod 2^k` is certified, if any. -/
def certStep (r k : ℕ) : Option ℕ :=
  (List.range' 1 k).find? fun i => 3 ^ oddCount r i < 2 ^ i

theorem certStep_sound {r k i : ℕ} (h : certStep r k = some i) :
    1 ≤ i ∧ i ≤ k ∧ 3 ^ oddCount r i < 2 ^ i := by
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_range'_1] at hmem
  simp only [decide_eq_true_eq] at hp
  exact ⟨hmem.1, by omega, hp⟩

/-- Finite check for the members of certified classes that `drop_of_certified` does not cover
(those with `m + r ≤ T^[i] r`). -/
def smallCheck (k : ℕ) : Bool :=
  (List.range (2 ^ k)).all fun r =>
    (certStep r k).all fun i =>
      (List.range (T^[i] r + 1 - r)).all fun m =>
        decide (r + 2 ^ k * m < 2 ∨ T^[i] (r + 2 ^ k * m) < r + 2 ^ k * m)

theorem smallCheck_sound {k : ℕ} (hk : smallCheck k = true) {r i m : ℕ} (hr : r < 2 ^ k)
    (hi : certStep r k = some i) (hm : m + r ≤ T^[i] r) :
    r + 2 ^ k * m < 2 ∨ T^[i] (r + 2 ^ k * m) < r + 2 ^ k * m := by
  simp only [smallCheck, List.all_eq_true, List.mem_range] at hk
  have := hk r hr
  rw [hi, Option.all_some, List.all_eq_true] at this
  simpa using this m (List.mem_range.2 (by omega))

/-- **Main theorem.** If `smallCheck k` holds, every `n ≥ 2` in a class certified at step `i`
satisfies `T^[i] n < n`. -/
theorem drop_of_certStep {k : ℕ} (hk : smallCheck k = true) {n i : ℕ} (hn : 2 ≤ n)
    (hi : certStep (n % 2 ^ k) k = some i) : 1 ≤ i ∧ i ≤ k ∧ T^[i] n < n := by
  obtain ⟨h1, h2, hc⟩ := certStep_sound hi
  refine ⟨h1, h2, ?_⟩
  have hn' : n = n % 2 ^ k + 2 ^ k * (n / 2 ^ k) := (Nat.mod_add_div n (2 ^ k)).symm
  rw [hn']
  by_cases hm : T^[i] (n % 2 ^ k) < n / 2 ^ k + n % 2 ^ k
  · exact drop_of_certified h2 hc hm
  · rcases smallCheck_sound hk (m := n / 2 ^ k) (Nat.mod_lt _ (by positivity)) hi (by omega)
      with h | h
    · omega
    · exact h

/-! ## Concrete instances (checked by the kernel) -/

theorem smallCheck_10 : smallCheck 10 = true := by decide +kernel

/-- Survivors mod `2^k` for `k = 0..10` match OEIS A076227 (and `compute/`, experiment 002). -/
theorem survivor_counts :
    (List.range 11).map
        (fun k => ((List.range (2 ^ k)).filter fun r => certStep r k = none).length) =
      [1, 1, 1, 2, 3, 4, 8, 13, 19, 38, 64] := by decide +kernel

/-- Every `n ≥ 2` outside the classes `7, 11, 15 (mod 16)` drops below itself
within 4 steps of `T`. -/
theorem drop_mod_16 {n : ℕ} (hn : 2 ≤ n) (h : n % 16 ≠ 7 ∧ n % 16 ≠ 11 ∧ n % 16 ≠ 15) :
    ∃ i ≤ 4, T^[i] n < n := by
  have hk : smallCheck 4 = true := by decide +kernel
  have hcert : ∀ r < 16, r ≠ 7 → r ≠ 11 → r ≠ 15 → (certStep r 4).isSome := by decide +kernel
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1
    (hcert (n % 16) (Nat.mod_lt _ (by norm_num)) h.1 h.2.1 h.2.2)
  obtain ⟨-, h2, h3⟩ := drop_of_certStep hk hn hi
  exact ⟨i, h2, h3⟩

end Collatz
