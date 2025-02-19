import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Finset.Range
import Mathlib.Topology.Instances.Real.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Init.Notation
import LeanCopilot

open Real Polynomial Filter Topology BigOperators

noncomputable def TT (m : ℕ) :=
  Chebyshev.T ℝ (2^m)

noncomputable def ψ_term (m : ℕ) (r : ℝ): ℝ :=
  ((TT m).eval r) / (8^m)

noncomputable def ψₖ (k : ℕ) (r : ℝ): ℝ :=
  (3 / 7 : ℝ) + (8^(-k : ℤ) / 14 : ℝ) + (1 / 2 : ℝ) *
  (∑ m ∈ Finset.range (k + 1), ψ_term m r)

noncomputable def ψ (r : ℝ): ℝ :=
  (3 / 7 : ℝ) + (1 / 2 : ℝ) * (∑' m, ψ_term m r)

lemma TT_recursion (m : ℕ) :
  TT (m + 1) = 2 * (TT m)^2 - 1 := by
  rw [TT, TT]
  rw [Int.pow_succ 2 m]  -- Rewrite 2^(m+1) as 2^m * 2
  rw [mul_comm]          -- Rewrite 2^m * 2 as 2 * 2^m
  -- Apply T_mul to express T_{2 * 2^m} in terms of T_{2^m}
  rw [Chebyshev.T_mul ℝ 2 (2^m)]
  rw [Chebyshev.T_two ℝ] -- Expand T_2 to 2x^2 - 1
  simp

-- Prove that -1/2 and 1 are fixed points of the recurrence for all m : ℕ
lemma fixed_points (m : ℕ) (r : ℝ) (hr : r = -1/2 ∨ r = 1) :
  (TT m).eval r = r := by
  unfold TT
  induction m with
  | zero =>
    -- Base case: T 1 = X, so T 1(-1/2) = -1/2 and T 1(1) = 1
    cases hr with
    | inl hr_neg_half =>
      simp [hr_neg_half, Chebyshev.T_one]
    | inr hr_one =>
      simp [hr_one, Chebyshev.T_one]
  | succ m ih =>
    -- Inductive case: T (m + 1) = 2 * T m^2 - 1
    rw [Int.pow_succ 2 m, mul_comm, Chebyshev.T_mul ℝ 2 (2^m), Chebyshev.T_two ℝ]
    cases hr
    · -- r = -1/2
      simp [ih, Chebyshev.T_two, Chebyshev.T_one]
      subst r
      ring_nf
    · -- r = 1
      simp [ih, Chebyshev.T_two, Chebyshev.T_one]
      subst r
      ring_nf

-- Prove that the fixed points are repellent
lemma repellent_fixed_points (m : ℕ) (r : ℝ) (hr : r = -1/2 ∨ r = 1) :
  |(Polynomial.derivative (TT m)).eval r| > 1 := by
  sorry

lemma geometric_sum (b : ℝ) (h : b > 1) (j k : ℕ) (hjk : j ≤ k) :
    ∑ m ∈ Finset.Ico j (k + 1), (1 / b)^(m) = (b^(1 - j) - b^(-k : ℤ)) / (b - 1) := by
  have hb : b ≠ 1 := by linarith
  have hb_pos : 0 < b := by linarith

  rw [geom_sum_Ico]
  · sorry
  · simpa using hb
  · exact Nat.le_succ_of_le hjk

lemma abs_TT_le_one (r: ℝ) (hr: |r| ≤ 1):
    ∀ m: ℕ, |(TT m).eval r| ≤ 1:= by
  intro m
  induction m with
  | zero =>
    unfold TT
    ring_nf
    simp [Chebyshev.T_one, hr]
  | succ m ih =>
    rw [TT_recursion]
    simp_all only [eval_sub, eval_mul, eval_ofNat, eval_pow, eval_one]
    rw [abs]
    simp_all only [neg_sub, sup_le_iff, tsub_le_iff_right]
    simp_all only [le_add_iff_nonneg_right, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    apply And.intro
    · norm_num
      simp_all only
    · positivity

lemma ψ_term_bound (m : ℕ) (r : ℝ) (hr : |r| ≤ 1) :
    |ψ_term m r| ≤ 1 / (8^m) := by
  unfold ψ_term
  rw [abs_div]
  field_simp
  ring_nf
  have h_bound : |(TT m).eval r| ≤ 1 := by
    apply abs_TT_le_one
    exact hr
  have h_pos : 0 < (8: ℝ)^m := by
    apply pow_pos
    norm_num
  simpa

lemma ψ_summable (r : ℝ) (hr : |r| ≤ 1) :
    Summable (fun m => ψ_term m r) := by
  -- Step 1: Bound the terms of the series
  have h_bound : ∀ m, |ψ_term m r| ≤ 1 / (8^m) := by
    intro m
    exact ψ_term_bound m r hr

  -- Step 2: Show that the bounding series is summable
  have h_summable : Summable (fun m => 1 / (8^m : ℝ)) := by
    apply summable_one_div_pow_of_le
    linarith
    exact le_refl

  -- Step 3: Apply the comparison test
  exact Summable.of_norm_bounded _ h_summable h_bound

-- From https://leanprover-community.github.io/theories/topology.html#filters
example : Tendsto (fun x : ℝ ↦ 1 / x) atTop (𝓝 0) := by
  simp
  apply Tendsto.inv_tendsto_atTop
  apply tendsto_id
