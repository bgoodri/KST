import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Topology.Instances.Real.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Init.Notation
import LeanCopilot

open Real Polynomial Filter Topology BigOperators

lemma degree_Tⱼ_eq_j (j : ℤ) (hj: j ≥ 0): (Chebyshev.T ℝ j).natDegree = j := by
  induction j using Chebyshev.induct with
  | zero =>
    -- T 0 = 1, degree is 0
    simp [Chebyshev.T_zero, natDegree_one]
  | one =>
    -- T 1 = X, degree is 1
    simp [Chebyshev.T_one, natDegree_X]
  | add_two j ih1 ih2 =>
    -- T (j + 2) = 2 * X * T (j + 1) - T j
    rw [Chebyshev.T_add_two ℝ j, natDegree_sub_eq_left_of_natDegree_lt]
    rw [natDegree_C_mul, natDegree_mul_X]
    · -- Degree of 2 * X * T (j + 1) is 1 + (j + 1) = j + 2
      rw [natDegree_mul_X, ih1]
      simp [Nat.succ_eq_add_one]
    · -- Degree of T j is j, which is less than j + 2
      rw [ih2]
      exact Nat.lt_succ_self j
  | neg_add_one hj =>
    -- Since j is non-negative, this case is unreachable
    -- TODO: Figure out how to drop h
    exfalso
    linarith

lemma leading_coeff_Tⱼ (j : ℤ) (hj : j > 0) :
    (Chebyshev.T ℝ j).leadingCoeff = 2 ^ (j.toNat - 1) := by
  induction j using Polynomial.Chebyshev.induct with
  | zero =>
    -- T 0 = 1, but j > 0, so this case is unreachable
    exact (lt_irrefl 0 hj).elim
  | one =>
    -- T 1 = X, leading coefficient is 1 = 2^(1-1)
    simp [Chebyshev.T_one, leadingCoeff_X, Nat.sub_self, pow_zero]
  | add_two j ih1 ih2 =>
    -- T (j + 2) = 2 * X * T (j + 1) - T j
    rw [Chebyshev.T_add_two ℝ j, leadingCoeff_sub_of_degree_lt]
    rw [leadingCoeff_mul_X, leadingCoeff_mul]
    · -- Leading coefficient of 2 * X * T (j + 1) is 2 * 1 * leadingCoeff(T (j + 1))
      rw [leadingCoeff_X, mul_one, ih1 (by linarith)]
      rw [Nat.succ_eq_add_one, Int.toNat_add_one_of_nonneg]
      · -- Simplify 2 * 2^(j) = 2^(j + 1)
        rw [pow_succ]
      · -- j + 1 > 0 since j > -1 (from induction hypothesis)
        linarith
    · -- Degree of T j is less than degree of 2 * X * T (j + 1)
      rw [degree_T ℝ j, degree_T ℝ (j + 1), Int.natAbs_ofNat, Int.natAbs_ofNat]
      exact Nat.lt_succ_self (j.toNat)
  | neg_add_one j ih1 ih2 =>
    -- Since j > 0, this case is unreachable
    exact (lt_irrefl j (by linarith [hj])).elim

noncomputable def T_power_two (m : ℕ) :=
  Chebyshev.T ℝ (2^m)

lemma T_power_two_recursion (m : ℕ) :
  T_power_two (m + 1) = 2 * (T_power_two m)^2 - 1 := by
  unfold T_power_two
  rw [Int.pow_succ 2 m]  -- Rewrite 2^(m+1) as 2^m * 2
  rw [mul_comm]          -- Rewrite 2^m * 2 as 2 * 2^m
  -- Apply T_mul to express T_{2 * 2^m} in terms of T_{2^m}
  rw [Chebyshev.T_mul ℝ 2 (2^m)]
  rw [Chebyshev.T_two ℝ] -- Expand T_2 to 2x^2 - 1
  simp

noncomputable def ψ_term (m : ℕ) (r : ℝ): ℝ :=
  ((T_power_two m).eval r) / (8^m)

noncomputable def ψₖ (k : ℕ) (r : ℝ): ℝ :=
  (3 / 7 : ℝ) + (1 / (7 * 2^(3 * k + 1)) : ℝ) + (1 / 2 : ℝ) *
  (∑ m ∈ Finset.range (k + 1), ψ_term m r)

noncomputable def ψ (r : ℝ): ℝ :=
  (3 / 7 : ℝ) + (1 / 2 : ℝ) * (∑' m, ψ_term m r)

lemma geometric_sum (b : ℝ) (h : b > 1) (j k : ℕ) (hjk : j ≤ k) :
    ∑ m ∈ Finset.Icc j k, b^(-(m : ℤ)) = (b^(1 - j) - b^(-k : ℤ)) / (b - 1) := by

  induction k with
  | zero =>
    rw [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_bot, add_zero]
    simp [h]
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (Nat.le_of_succ_le hjk)]
    have : (k : ℤ) + 1 = (k + 1 : ℤ) := by norm_cast
    rw [this, pow_neg, pow_neg, sub_div, sub_div, sub_sub, sub_sub, add_comm, add_sub_assoc, add_sub_assoc]
    simp [h]


-- From https://leanprover-community.github.io/theories/topology.html#filters
example : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 0) := by
  simp
  apply Tendsto.inv_tendsto_atTop
  apply tendsto_id


lemma ψₖ_converges_to_ψ (r : ℝ) :
  Filter.Tendsto (fun k => ψₖ k r) Filter.atTop (𝓝 (ψ r)) := by
  unfold ψ ψₖ
  apply Tendsto.add
  simp
  sorry

def 𝕋 := Set.Icc (-1) 1

lemma T_maps_interval (j : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (-1) 1) :
    (Polynomial.Chebyshev.T ℝ j).eval t ∈ Set.Icc (-1) 1 := by
  rw [Set.mem_Icc] at ht
  obtain ⟨h_le_neg_one, h_le_one⟩ := ht
  let θ := Real.arccos t
  have hθ : t = cos θ := by
    rw [Real.cos_arccos h_le_neg_one h_le_one]
  rw [hθ, Polynomial.Chebyshev.T_real_cos θ j]
  exact ⟨neg_one_le_cos (j * θ), cos_le_one (j * θ)⟩

lemma ψ_term_bound (m: ℕ) (t: ℝ) (ht: t ∈ Set.Icc (-1) 1):
  |ψ_term m t| ≤ 1 / (8^m: ℝ):= by
  unfold ψ_term
  have hT_eval: (T_power_two m).eval t ∈ Set.Icc (-1) 1:= by
    apply T_maps_interval
    exact ht
  rw [Set.mem_Icc] at hT_eval
  obtain ⟨h_le_neg_one, h_le_one⟩:= hT_eval
  have h_abs_T: |(T_power_two m).eval t| ≤ 1:= by
    apply abs_le.mpr
    constructor
    · exact h_le_neg_one
    · exact h_le_one
  have h_abs_8m: |(8: ℝ)^m| = 8^m:= by
    rw [abs_of_pos (pow_pos (by norm_num) m)]
  have h_pos_8m: 0 < (8: ℝ)^m:= by
    apply pow_pos
    norm_num
  calc |ψ_term m t| = |((T_power_two m).eval t) / 8^m|:= by rfl
                  _ = |(T_power_two m).eval t| / |8^m|:= by rw [abs_div]
                  _ = |(T_power_two m).eval t| / 8^m:= by rw [h_abs_8m]
                  _ ≤ 1 / 8^m:= by
                    apply div_le_div_of_nonneg_right h_abs_T (le_of_lt h_pos_8m)

lemma ψ_summable (t : ℝ) (ht : t ∈ Set.Icc (-1) 1) :
  Summable (fun m => ψ_term m t) := by
  apply Summable.of_abs
  intro m
  exact ψ_term_bound m t ht
