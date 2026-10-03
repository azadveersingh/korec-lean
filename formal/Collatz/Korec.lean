import Collatz.Residues
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Korec 1994: density one for `T^k(n) < n^θ`, `θ > log 3 / log 4`

Main result: `korec_density_one`. Blueprint: `notes/ideas/korec1994-formalization.md`; lemma numbers
below refer to it. We follow the dyadic-block variant: lemmas 2, 3 and 8a are merged into the
generating function `sum_pow_oddCount`, the tail bound is a Chernoff tilt (`exists_tilt`), and the
Cesàro step is replaced by an explicit geometric bound, so no `p/q` core is needed.
Source: I. Korec, *A density estimate for the 3x+1 problem*, Math. Slovaca 44 (1994) 85–89.
-/

open Filter Topology

namespace Collatz

/-- Lemma 1. The first `k` parities of `r + 2^k m` agree with those of `r`. -/
theorem oddCount_add_two_pow_mul (r m k : ℕ) :
    ∀ i, i ≤ k → oddCount (r + 2 ^ k * m) i = oddCount r i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    obtain ⟨d, hd⟩ : ∃ d, k - i = d + 1 := ⟨k - i - 1, by omega⟩
    rw [oddCount, oddCount, ih (by omega), T_iterate_affine r m k i (by omega), hd, pow_succ,
      show 3 ^ oddCount r i * (2 ^ d * 2) * m = 2 * (3 ^ oddCount r i * 2 ^ d * m) by ring]
    generalize 3 ^ oddCount r i * 2 ^ d * m = c
    omega

/-- Lemma 4. Exact orbit upper bound: `2^i T^i(x) + 2^i ≤ 3^e (x + 2^i)`, `e` = odd steps. -/
theorem two_pow_mul_T_iterate_add_le (x : ℕ) :
    ∀ i, 2 ^ i * T^[i] x + 2 ^ i ≤ 3 ^ oddCount x i * (x + 2 ^ i)
  | 0 => by simp [oddCount]
  | i + 1 => by
    have ih := two_pow_mul_T_iterate_add_le x i
    rw [Function.iterate_succ_apply', oddCount, pow_succ 2 i, pow_add]
    generalize T^[i] x = y at ih ⊢
    generalize 2 ^ i = P at ih ⊢
    have hE : 1 ≤ 3 ^ oddCount x i := Nat.one_le_pow _ _ (by norm_num)
    generalize 3 ^ oddCount x i = E at ih hE ⊢
    rcases Nat.mod_two_eq_zero_or_one y with h | h
    · obtain ⟨z, rfl⟩ : ∃ z, y = 2 * z := ⟨y / 2, by omega⟩
      rw [show T (2 * z) = z by unfold T; split_ifs; omega, h, pow_zero, mul_one]
      nlinarith [Nat.mul_le_mul_right P hE]
    · obtain ⟨z, rfl⟩ : ∃ z, y = 2 * z + 1 := ⟨y / 2, by omega⟩
      rw [show T (2 * z + 1) = 3 * z + 2 by unfold T; split_ifs <;> omega, h, pow_one]
      nlinarith [Nat.zero_le (E * P)]

/-- Lemma 5. On `[0, 2^(L+1))`, `L` steps give `T^L(n) < 3^(e+1)`. -/
theorem T_iterate_lt_three_pow {n L : ℕ} (hn : n < 2 ^ (L + 1)) :
    T^[L] n < 3 ^ (oddCount n L + 1) := by
  have h4 := two_pow_mul_T_iterate_add_le n L
  have hP : 0 < 2 ^ L := by positivity
  have hE : 0 < 3 ^ oddCount n L := by positivity
  rw [pow_succ] at hn ⊢
  have h3 : 3 ^ oddCount n L * (n + 2 ^ L) < 3 ^ oddCount n L * (3 * 2 ^ L) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hE
  have : 2 ^ L * T^[L] n < 2 ^ L * (3 ^ oddCount n L * 3) := by nlinarith
  exact Nat.lt_of_mul_lt_mul_left this

/-- Lemmas 2, 3 and 8a merged: the generating function of `oddCount · L` over the complete
residue system `[0, 2^L)` is `(1 + t)^L`. (Pascal step: `r` and `r + 2^L` share their first `L`
parities and differ in the next one.) -/
theorem sum_pow_oddCount {R : Type*} [CommSemiring R] (t : R) :
    ∀ L, ∑ r ∈ Finset.range (2 ^ L), t ^ oddCount r L = (1 + t) ^ L
  | 0 => by simp [oddCount]
  | L + 1 => by
    rw [pow_succ 2 L, mul_two, Finset.sum_range_add, pow_succ, ← sum_pow_oddCount t L,
      Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h1 := oddCount_add_two_pow_mul r 1 L L le_rfl
    have h2 := T_iterate_affine r 1 L L le_rfl
    simp only [Nat.sub_self, pow_zero, mul_one] at h2
    rw [mul_one] at h1
    rw [add_comm (2 ^ L) r, oddCount, oddCount, h1, h2]
    have h3 : 3 ^ oddCount r L % 2 = 1 := Nat.pow_mod 3 _ 2 ▸ by simp
    rcases Nat.mod_two_eq_zero_or_one (T^[L] r) with h | h
    · rw [h, show (3 ^ oddCount r L + T^[L] r) % 2 = 1 by omega]; ring
    · rw [h, show (3 ^ oddCount r L + T^[L] r) % 2 = 0 by omega]; ring

/-- Lemma 8b. For `β > 1/2` there is a tilt `t > 1` with `1 + t < 2 t^β`. -/
theorem exists_tilt {β : ℝ} (hβ : 1 / 2 < β) : ∃ t : ℝ, 1 < t ∧ 1 + t < 2 * t ^ β := by
  set b := min β (3 / 4)
  have hb1 : 1 / 2 < b := lt_min hβ (by norm_num)
  have hb2 : b ≤ 3 / 4 := min_le_right _ _
  set s := (2 * b - 1) / (2 * (1 - b))
  have hs : 0 < s := div_pos (by linarith) (by linarith)
  have hb3 : (1 : ℝ) - b ≠ 0 := by linarith
  have hs' : (1 - b) * s = (2 * b - 1) / 2 := by
    simp only [s]; field_simp
  have ht : 1 < 1 + s := by linarith
  refine ⟨1 + s, ht, ?_⟩
  have hB : (1 + s) ^ (1 - b) ≤ 1 + (1 - b) * s :=
    rpow_one_add_le_one_add_mul_self (by linarith) (by linarith) (by linarith)
  have hsplit : (1 + s) ^ b * (1 + s) ^ (1 - b) = 1 + s := by
    rw [← Real.rpow_add (by linarith), add_sub_cancel, Real.rpow_one]
  have hpos : 0 < (1 + s) ^ b := Real.rpow_pos_of_pos (by linarith) _
  have hb : 1 + (1 + s) < 2 * (1 + s) ^ b := by
    have hD : 0 < 1 + (1 - b) * s := by nlinarith
    have hle : 1 + s ≤ (1 + s) ^ b * (1 + (1 - b) * s) := by
      calc 1 + s = (1 + s) ^ b * (1 + s) ^ (1 - b) := hsplit.symm
        _ ≤ (1 + s) ^ b * (1 + (1 - b) * s) := mul_le_mul_of_nonneg_left hB hpos.le
    have hlt : (1 + (1 + s)) * (1 + (1 - b) * s) < 2 * (1 + s) := by nlinarith
    by_contra hcon
    push Not at hcon
    nlinarith [mul_le_mul_of_nonneg_right hcon hD.le]
  calc 1 + (1 + s) < 2 * (1 + s) ^ b := hb
    _ ≤ 2 * (1 + s) ^ β := by
      gcongr
      · exact ht.le
      · exact min_le_left _ _

/-! ## Density bookkeeping -/

section Density

open Classical

/-- The set of Korec's theorem: `n` whose orbit eventually goes below `n^θ`. -/
def korecSet (θ : ℝ) : Set ℕ := {n | ∃ k, ((T^[k] n : ℕ) : ℝ) < (n : ℝ) ^ θ}

/-- Bad residues mod `2^L`: those whose first `L` steps have too many odd values. -/
noncomputable def badRes (θ : ℝ) (L : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ L)).filter fun r => (2 : ℝ) ^ (θ * L) < 3 ^ (oddCount r L + 1)

/-- Number of `n < N` outside the Korec set. -/
noncomputable def compCount (θ : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => n ∉ korecSet θ).card

/-- Lemma 8 (Chernoff form). Bad residues are rare: `#bad · t^(βL) ≤ t (1+t)^L`,
`β = θ log 2 / log 3`, for every tilt `t ≥ 1`. -/
theorem card_badRes_mul_le {θ t : ℝ} (ht : 1 ≤ t) (L : ℕ) :
    (badRes θ L).card * t ^ (θ * Real.log 2 / Real.log 3 * L) ≤ t * (1 + t) ^ L := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have key : ∀ r ∈ badRes θ L,
      t ^ (θ * Real.log 2 / Real.log 3 * L) ≤ t ^ (oddCount r L + 1) := by
    intro r hr
    rw [badRes, Finset.mem_filter] at hr
    have hlog := Real.log_lt_log (by positivity) hr.2
    rw [Real.log_rpow (by norm_num), Real.log_pow] at hlog
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le ht ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hl3]
    push_cast at hlog ⊢
    linarith
  calc (badRes θ L).card * t ^ (θ * Real.log 2 / Real.log 3 * L)
      = ∑ _r ∈ badRes θ L, t ^ (θ * Real.log 2 / Real.log 3 * L) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ badRes θ L, t ^ (oddCount r L + 1) := Finset.sum_le_sum key
    _ ≤ ∑ r ∈ Finset.range (2 ^ L), t ^ (oddCount r L + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => by positivity
    _ = t * (1 + t) ^ L := by
        simp_rw [pow_succ]
        rw [← Finset.sum_mul, sum_pow_oddCount]; ring

/-- Lemmas 5–6 (real form). A good residue `r` gives `2^L + r ∈ korecSet θ`, via `L` steps. -/
theorem mem_korecSet_of_good {θ : ℝ} (hθ : 0 ≤ θ) {L r : ℕ} (hr : r < 2 ^ L)
    (hgood : ¬ (2 : ℝ) ^ (θ * L) < 3 ^ (oddCount r L + 1)) : 2 ^ L + r ∈ korecSet θ := by
  refine ⟨L, ?_⟩
  have h1 := oddCount_add_two_pow_mul r 1 L L le_rfl
  rw [mul_one, add_comm] at h1
  have h5 := T_iterate_lt_three_pow (n := 2 ^ L + r) (L := L) (by rw [pow_succ]; omega)
  rw [h1] at h5
  push Not at hgood
  calc ((T^[L] (2 ^ L + r) : ℕ) : ℝ) < ((3 ^ (oddCount r L + 1) : ℕ) : ℝ) := by exact_mod_cast h5
    _ = (3 : ℝ) ^ (oddCount r L + 1) := by push_cast; rfl
    _ ≤ 2 ^ (θ * L) := hgood
    _ = ((2 : ℝ) ^ L) ^ θ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
    _ ≤ ((2 ^ L + r : ℕ) : ℝ) ^ θ :=
        Real.rpow_le_rpow (by positivity)
          (by push_cast; linarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]) hθ

/-- Lemma 9 + dyadic decomposition: below `2^K`, the exceptions are `0` plus the bad residues
of each block `[2^L, 2^(L+1))`, `L < K`. -/
theorem compCount_two_pow_le {θ : ℝ} (hθ : 0 ≤ θ) :
    ∀ K, compCount θ (2 ^ K) ≤ 1 + ∑ L ∈ Finset.range K, (badRes θ L).card
  | 0 => by
    simp only [compCount, pow_zero, Finset.range_zero, Finset.sum_empty, add_zero]
    exact (Finset.card_filter_le _ _).trans (by simp)
  | K + 1 => by
    have ih := compCount_two_pow_le hθ K
    have hB : ((Finset.range (2 ^ K)).filter fun r => 2 ^ K + r ∉ korecSet θ).card ≤
        (badRes θ K).card := by
      refine Finset.card_le_card fun r hr => ?_
      rw [Finset.mem_filter] at hr
      rw [badRes, Finset.mem_filter]
      refine ⟨hr.1, ?_⟩
      by_contra hgood
      exact hr.2 (mem_korecSet_of_good hθ (Finset.mem_range.1 hr.1) hgood)
    rw [compCount] at ih ⊢
    rw [Finset.card_filter] at ih hB ⊢
    rw [pow_succ, mul_two, Finset.sum_range_add, Finset.sum_range_succ]
    omega

/-- Monotonicity of the exception count. -/
theorem compCount_mono (θ : ℝ) {M N : ℕ} (h : M ≤ N) : compCount θ M ≤ compCount θ N := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

/-- **Power saving (quantitative core).** For `θ > log 3 / log 4` there are `t > 0` and `g < 2`
with at most `1 + 2 t g^K` exceptions to Korec's property below `2^K`. -/
theorem exists_geom_bound (θ : ℝ) (hθ : Real.log 3 / Real.log 4 < θ) :
    ∃ t g : ℝ, 1 < t ∧ 3 / 2 ≤ g ∧ g < 2 ∧
      ∀ K, (compCount θ (2 ^ K) : ℝ) ≤ 1 + 2 * t * g ^ K := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [hl4, div_lt_iff₀ (by positivity)] at hθ
  have hθ0 : 0 < θ := by nlinarith
  set β := θ * Real.log 2 / Real.log 3 with hβdef
  have hβ : 1 / 2 < β := by rw [hβdef, lt_div_iff₀ hl3]; linarith
  obtain ⟨t, ht1, htβ⟩ := exists_tilt hβ
  have htβpos : 0 < t ^ β := Real.rpow_pos_of_pos (by linarith) _
  set g := max ((1 + t) / t ^ β) (3 / 2)
  have hg2 : g < 2 := max_lt ((div_lt_iff₀ htβpos).2 htβ) (by norm_num)
  have hg1 : 3 / 2 ≤ g := le_max_right _ _
  -- bad residues in block `L`: at most `t g^L`
  have hbad : ∀ L, ((badRes θ L).card : ℝ) ≤ t * g ^ L := by
    intro L
    have h := card_badRes_mul_le (θ := θ) ht1.le L
    rw [← hβdef, Real.rpow_mul (by linarith), Real.rpow_natCast] at h
    have hpos : 0 < (t ^ β) ^ L := pow_pos htβpos L
    calc ((badRes θ L).card : ℝ) ≤ t * (1 + t) ^ L / (t ^ β) ^ L := by
          rw [le_div_iff₀ hpos]; linarith
      _ = t * ((1 + t) / t ^ β) ^ L := by rw [div_pow]; ring
      _ ≤ t * g ^ L := by
          gcongr
          exact le_max_left _ _
  -- exceptions below `2^K`: at most `1 + 2 t g^K`
  have hK : ∀ K, (compCount θ (2 ^ K) : ℝ) ≤ 1 + 2 * t * g ^ K := by
    intro K
    have h := compCount_two_pow_le hθ0.le K
    have hsum : ∑ L ∈ Finset.range K, ((badRes θ L).card : ℝ) ≤ 2 * t * g ^ K := by
      calc ∑ L ∈ Finset.range K, ((badRes θ L).card : ℝ) ≤ ∑ L ∈ Finset.range K, t * g ^ L :=
            Finset.sum_le_sum fun L _ => hbad L
        _ = t * ((g ^ K - 1) / (g - 1)) := by
            rw [← Finset.mul_sum, geom_sum_eq (by linarith)]
        _ ≤ 2 * t * g ^ K := by
            rw [mul_div_assoc', div_le_iff₀ (by linarith)]
            have ht0 : 0 ≤ t * g ^ K := by positivity
            nlinarith [mul_nonneg ht0 (show 0 ≤ 2 * (g - 1) - 1 by linarith)]
    calc (compCount θ (2 ^ K) : ℝ) ≤ ((1 + ∑ L ∈ Finset.range K, (badRes θ L).card : ℕ) : ℝ) := by
          exact_mod_cast h
      _ ≤ 1 + 2 * t * g ^ K := by push_cast; linarith
  exact ⟨t, g, ht1, hg1, hg2, hK⟩

/-- **Power saving, in `N`.** The exceptions to Korec's property below `N` number at most
`C N^δ` for some `δ < 1` (depending on `θ`). -/
theorem compCount_le_rpow (θ : ℝ) (hθ : Real.log 3 / Real.log 4 < θ) :
    ∃ C δ : ℝ, 0 ≤ C ∧ δ < 1 ∧ ∀ N : ℕ, 1 ≤ N → (compCount θ N : ℝ) ≤ C * (N : ℝ) ^ δ := by
  obtain ⟨t, g, ht1, hg1, hg2, hK⟩ := exists_geom_bound θ hθ
  have hg0 : 0 < g := by linarith
  set δ := Real.logb 2 g
  have hδ1 : δ < 1 := by
    have := Real.logb_lt_logb (b := 2) (by norm_num) hg0 hg2
    rwa [Real.logb_self_eq_one (by norm_num)] at this
  have hδ0 : 0 ≤ δ := Real.logb_nonneg (by norm_num) (by linarith)
  have hgδ : (2 : ℝ) ^ δ = g := Real.rpow_logb (by norm_num) (by norm_num) hg0
  refine ⟨(1 + 2 * t) * g, δ, by positivity, hδ1, fun N hN => ?_⟩
  set K := Nat.log 2 N + 1
  have hNK : N ≤ 2 ^ K := (Nat.lt_pow_succ_log_self (by norm_num) N).le
  have hKN : 2 ^ K ≤ 2 * N := by
    rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
  have hc := (show (compCount θ N : ℝ) ≤ compCount θ (2 ^ K) by
    exact_mod_cast compCount_mono θ hNK).trans (hK K)
  have hgK : g ^ K = ((2 : ℝ) ^ K) ^ δ := by
    rw [← hgδ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (2 : ℝ) K,
      ← Real.rpow_mul (by norm_num), mul_comm]
  have h2K : ((2 : ℝ) ^ K) ^ δ ≤ (2 * N) ^ δ :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hKN) hδ0
  have h2N : (2 * (N : ℝ)) ^ δ = g * (N : ℝ) ^ δ := by
    rw [Real.mul_rpow (by norm_num) (by positivity), hgδ]
  have h1g : 1 ≤ g ^ K := one_le_pow₀ (by linarith)
  calc (compCount θ N : ℝ) ≤ 1 + 2 * t * g ^ K := hc
    _ ≤ (1 + 2 * t) * g ^ K := by nlinarith
    _ ≤ (1 + 2 * t) * (g * (N : ℝ) ^ δ) := by
        rw [hgK, ← h2N]; exact mul_le_mul_of_nonneg_left h2K (by positivity)
    _ = (1 + 2 * t) * g * (N : ℝ) ^ δ := by ring

/-- **Korec (1994), Theorem 1.** For every `θ > log 3 / log 4`, the set of `n` with
`T^k(n) < n^θ` for some `k` has natural density `1`. -/
theorem korec_density_one (θ : ℝ) (hθ : Real.log 3 / Real.log 4 < θ) :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => n ∈ korecSet θ).card : ℝ) / N)
      atTop (𝓝 1) := by
  obtain ⟨t, g, ht1, hg1, hg2, hK⟩ := exists_geom_bound θ hθ
  -- ratio bound in terms of `K = log₂ N + 1`
  set f : ℕ → ℝ := fun K => 2 * (1 / 2) ^ K + 4 * t * (g / 2) ^ K
  have hf : Tendsto f atTop (𝓝 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := g / 2) (by linarith) (by linarith)
    have := (h1.const_mul 2).add (h2.const_mul (4 * t))
    simp only [mul_zero, add_zero] at this
    exact this
  have hlog : Tendsto (fun N => Nat.log 2 N + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      (tendsto_atTop_atTop.2 fun K => ⟨2 ^ K, fun N hN => Nat.le_log_of_pow_le (by norm_num) hN⟩)
  have hratio : ∀ N : ℕ, 1 ≤ N → (compCount θ N : ℝ) / N ≤ f (Nat.log 2 N + 1) := by
    intro N hN
    set K := Nat.log 2 N + 1
    have hNK : N ≤ 2 ^ K := (Nat.lt_pow_succ_log_self (by norm_num) N).le
    have hKN : 2 ^ K ≤ 2 * N := by
      rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
    have hc := (show (compCount θ N : ℝ) ≤ compCount θ (2 ^ K) by
      exact_mod_cast compCount_mono θ hNK).trans (hK K)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hKN' : (2 : ℝ) ^ K ≤ 2 * N := by exact_mod_cast hKN
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    rw [div_le_iff₀ hNpos]
    have hf' : f K * 2 ^ K = 2 + 4 * t * g ^ K := by
      simp only [f, div_pow, one_pow]; field_simp
    have hfpos : 0 ≤ f K := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hKN' hfpos]
  have hcomp : Tendsto (fun N : ℕ => (compCount θ N : ℝ) / N) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf.comp hlog) ?_ ?_
    · exact Eventually.of_forall fun N => by positivity
    · exact eventually_atTop.2 ⟨1, fun N hN => hratio N hN⟩
  have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hcomp
  rw [sub_zero] at hsub
  refine hsub.congr' (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range N) (fun n => n ∈ korecSet θ)
  rw [Finset.card_range] at hsplit
  have : (((Finset.range N).filter fun n => n ∈ korecSet θ).card : ℝ) + compCount θ N = N := by
    rw [compCount]; exact_mod_cast hsplit
  dsimp only
  field_simp
  linarith

/-- **Terras (1976) / Everett (1977)** as the case `θ = 1`: almost every `n` has `T^k(n) < n`
for some `k` (natural density 1). -/
theorem terras_density_one :
    Tendsto (fun N : ℕ => (((Finset.range N).filter fun n => ∃ k, T^[k] n < n).card : ℝ) / N)
      atTop (𝓝 1) := by
  have h := korec_density_one 1 (by
    rw [div_lt_one (Real.log_pos (by norm_num))]
    exact Real.log_lt_log (by norm_num) (by norm_num))
  refine h.congr fun N => ?_
  have hf : ((Finset.range N).filter fun n => n ∈ korecSet 1) =
      (Finset.range N).filter fun n => ∃ k, T^[k] n < n :=
    Finset.filter_congr fun n _ => by
      simp only [korecSet, Set.mem_ofPred_eq, Real.rpow_one, Nat.cast_lt]
  rw [hf]

end Density

end Collatz
