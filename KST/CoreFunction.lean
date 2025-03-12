import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- import LeanCopilot

open Real Polynomial Filter Topology BigOperators Finset

variable (n : ℕ) [Fact (1 < n)]
def 𝕀 : Set ℝ := Set.Icc 0 1

noncomputable def TT (m : ℕ) := Chebyshev.T ℝ (2^m)

noncomputable def ϕ_term (m : ℕ) (r : ℝ): ℝ := ((TT m).eval r) / (8^m)

noncomputable def ϕₖ (k : ℕ) (r : ℝ): ℝ :=
  (3 / 7 : ℝ) + (8^(-k : ℤ) / 14 : ℝ) + (1 / 2 : ℝ) *
  (∑ m ∈ Finset.range (k + 1), ϕ_term m r)

noncomputable def ϕ (r : ℝ): ℝ := (3 / 7 : ℝ) + (1 / 2 : ℝ) * (∑' m, ϕ_term m r)

variable (lambda : ℝ) [Fact (0 < lambda)]

def Λ (n : ℕ) (lambda : ℝ) := (∑ p ∈ Finset.range n, lambda^p)

noncomputable def ψ (lambda : ℝ) (p : ℕ) (q : ℕ) (n : ℕ) (xₚ : 𝕀) :=
  (lambda^p) / (Λ n lambda) * (ϕ (xₚ - (q / (2 * n) : ℝ)))


lemma TT_recursion (m : ℕ) : TT (m + 1) = 2 * (TT m)^2 - 1 := by {
  unfold TT              -- Express it in terms of Chebyshev.T
  rw [Int.pow_succ 2 m]  -- Rewrite 2^(m+1) as 2^m * 2
  rw [mul_comm]          -- Rewrite 2^m * 2 as 2 * 2^m
  -- Apply T_mul to express T_{2 * 2^m} in terms of T_2 and T_{2^m}
  rw [Chebyshev.T_mul ℝ 2 (2^m)]
  rw [Chebyshev.T_two ℝ] -- Expand T_2 to 2x^2 - 1
  field_simp
}

lemma TT_bounds (r: ℝ) : ∀ m: ℕ, ((TT m).eval r)^2 ≤ 1 ↔ r^2 ≤ 1:= by
  intro m
  induction m with
  | zero =>
    unfold TT
    ring_nf
    simp [Chebyshev.T_one]
  | succ m ih =>
    rw [TT_recursion]
    field_simp
    rw [@abs_sub_le_iff]
    field_simp
    ring_nf
    constructor
    · -- Forward direction (→)
      intro h
      rcases h with ⟨h1, h2⟩
      have h1_simplified : (eval r (TT m))^2 ≤ 1 := by linarith [h1]
      rw [ih] at h1_simplified
      exact (sq_le_one_iff_abs_le_one r).mp h1_simplified
    · -- Backward direction (←)
      intro h
      have h' := (sq_le_one_iff_abs_le_one r).mpr h
      rw [← ih] at h'
      have h1 : (eval r (TT m))^2 * 2 ≤ 2 := by linarith [h']
      have h2 : 0 ≤ (eval r (TT m))^2 := by apply pow_two_nonneg
      exact ⟨h1, h2⟩

lemma fixed_points (m : ℕ) (r : ℝ) : (TT (m + 1)).eval r = (TT m).eval r ↔
  (TT m).eval r = -1/2 ∨ (TT m).eval r = 1 := by
  rw [TT_recursion]
  simp
  constructor
  · -- Forward direction (→): If r is a fixed point, then T_m(r) = -1/2 or T_m(r) = 1
    intro h
    ring_nf at h
    have h' : (eval r (TT m) + 1/2) * (eval r (TT m) - 1) = 0 := by
      linarith [show (eval r (TT m) + 1/2) = eval r (TT m) - (-1/2) by ring]
    rw [mul_eq_zero] at h'
    cases h' with
      | inl h1 => left; linarith [h1]
      | inr h2 => right; linarith [h2]
  · -- Backward direction (←): If T_m(r) = -1/2 or T_m(r) = 1, then r is a fixed point
    intro h
    cases h with
    | inl hl => rw [hl]; ring_nf
    | inr hr => rw [hr]; ring_nf

lemma geom_sum_neg_pow (b : ℝ) (h : 1 < b) (j k : ℕ) (hjk : j ≤ k + 1) :
    ∑ m ∈ Ico j (k + 1), b^(-(m : ℤ)) = (b^(1 - (j : ℤ)) - b^(-(k : ℤ))) / (b - 1) := by
  have hb : 1 / b ≠ 1 := by
    field_simp
    linarith
  have h_summand : ∀ m ∈ Ico j (k + 1), b^(-(m : ℤ)) = (1 / b)^(m : ℕ) := by
    intro m _
    rw [div_eq_mul_inv, zpow_neg]
    field_simp
  rw [sum_congr rfl h_summand]
  have hb_ne_zero : b ≠ 0 := by linarith
  rw [geom_sum_Ico']
  rw [one_div_pow, one_div_pow]
  ring_nf
  field_simp
  rw [mul_assoc, neg_div, div_mul_eq_div_mul_one_div, div_self hb_ne_zero, one_mul]
  rw [show -1 + b = b - 1 by ring]
  rw [show -(1 / (b ^ k * (b - 1))) = -1 / (b ^ k * (b - 1)) by ring]
  have hb_sub_one_ne_zero : b - 1 ≠ 0 := by linarith
  have hb_pow_mul_sub_ne_zero : b ^ k * (b - 1) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero k hb_ne_zero
    · exact hb_sub_one_ne_zero
  rw [show -1 / (b ^ k * (b - 1)) + b / (b ^ j * (b - 1)) = b / (b ^ j * (b - 1)) - 1 / (b ^ k * (b - 1)) by ring]
  simp +arith +decide
  rw [zpow_one_sub_natCast₀ hb_ne_zero j]
  field_simp
  exact hb
  exact hjk

lemma shifted_SOS (k : ℕ) (r : ℝ) : ϕₖ k r =
  (5 / 14 : ℝ) + (8^(-k : ℤ) / 7 : ℝ) + r / 2 + (1 / 8 : ℝ) *
  (∑ m ∈ Finset.range k, 8^(-m : ℤ) * (TT m).eval r ^ 2) := by
  -- Unfold the definitions of ϕₖ and ϕ_term
  unfold ϕₖ ϕ_term
  -- Pull out the m = 0 term from the sum
  rw [Finset.sum_range_succ'] -- Pulls out the m = 0 term
  rw [TT, pow_zero, pow_zero]
  simp +arith +decide
  -- Rewrite the sum using the recursion lemma
  conv_lhs => {
    rw [Finset.sum_congr rfl (fun k _ => by rw [TT_recursion k])]
    simp +arith +decide
  }
  -- Split the sum into two parts
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [show (2 * eval r (TT x) ^ 2 - 1) / 8 ^ (x + 1) =
        (2 * eval r (TT x) ^ 2) / 8 ^ (x + 1) - 1 / 8 ^ (x + 1) by ring_nf]
    )]
  rw [sum_sub_distrib]
  rw [mul_add]
  rw [show (2⁻¹ * (∑ x ∈ range k, 2 * eval r (TT x) ^ 2 / 8 ^ (x + 1) - ∑ x ∈ range k, 1 / 8 ^ (x + 1)) + 2⁻¹ * r) =
      2⁻¹ * (∑ x ∈ range k, 2 * eval r (TT x) ^ 2 / 8 ^ (x + 1) - ∑ x ∈ range k, 1 / 8 ^ (x + 1)) + 2⁻¹ * r by ring_nf]
  rw [mul_sub]
  rw [mul_sum]
  -- Simplify the first sum
  ring_nf

  rw [show ∑ x ∈ range k, (1 / 2 : ℝ) * (2 * eval r (TT x) ^ 2 / 8 ^ (x + 1)) =
      ∑ x ∈ range k, eval r (TT x) ^ 2 * (1 / 8) ^ (x + 1) by
    apply Finset.sum_congr rfl
    intro x hx
    field_simp]

  rw [Finset.sum_congr rfl (fun x _ => by
    rw [pow_add, div_pow, one_pow, pow_one, ← mul_assoc, ← mul_comm]
  )]
  conv =>
    pattern (∑ x ∈ range k, 1 / 8 ^ (x + 1))
    rw [Finset.sum_congr rfl (fun x _ => by
      rw [pow_add, div_mul_eq_div_div, pow_one, div_eq_mul_inv, mul_comm]
    )]
  ring_nf
  rw [← mul_sum, ← mul_sum]
  rw [show ∑ i ∈ range k, 1 / (8 ^ i : ℝ) = ∑ i ∈ range k, (1 / 8) ^ i by ring_nf]
  rw [geom_sum_eq (show (1 / 8 : ℝ) ≠ 1 by norm_num), one_div]

  -- Simplify the constants
  ring_nf
  field_simp
  ring

def 𝕋 : Set ℝ := Set.Icc (-1) 1

lemma ϕ_term_bound (m : ℕ) (t : ℝ) (ht : t ∈ 𝕋) : |ϕ_term m t| ≤ 1 / (8^m) := by {
  unfold ϕ_term
  rw [abs_div]
  field_simp
  ring_nf
  simp +arith +decide
  · have h_bound : |(TT m).eval t| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one, TT_bounds]
      rw [sq_le_one_iff_abs_le_one]
      exact abs_le.mpr ht
    linarith
}

lemma TT_pwr_representation (r : ℝ) (hr : 1 < |r|) (m : ℕ) : eval r (TT m) =
  ((r + sqrt (r^2 - 1))^(2^m) + (r - sqrt (r^2 - 1))^(2^m)) / 2 := by {
  induction m with
  | zero =>
    unfold TT
    simp [Chebyshev.T_one, pow_zero, pow_one]
  | succ m ih =>
    rw [TT_recursion m, eval_sub, eval_mul]
    field_simp
    rw [ih]
    have h_sqrt : 0 ≤ -1 + r^2 := by {
      field_simp [hr]
      linarith
    }
    field_simp [h_sqrt]
    rw [pow_succ, pow_succ]
    ring_nf
    -- Use the identity (r + sqrt(r^2 - 1)) * (r - sqrt(r^2 - 1)) = 1
    have h_product : (r + sqrt (r^2 - 1)) * (r - sqrt (r^2 - 1)) = 1 := by
      ring_nf
      rw [sq_sqrt h_sqrt]
      ring_nf
    have h_product_pow :
      (r + sqrt (r^2 - 1))^(2^m) * (r - sqrt (r^2 - 1))^(2^m) = 1 := by
        rw [← mul_pow, h_product, one_pow]
    have h_goal :
      (r - sqrt (r^2 - 1))^(2^m) * (r + sqrt (r^2 - 1))^(2^m) = 1 := by
        rw [mul_comm, h_product_pow]
    field_simp [h_product_pow, h_sqrt]
    ring_nf
    rw [show (r - √(-1 + r^2))^(2^m) * (r + √(-1 + r^2))^(2^m) =
          (r - √(r^2 - 1))^(2^m) * (r + √(r^2 - 1))^(2^m) by
      rw [show -1 + r^2 = r^2 - 1 by ring]]
    rw [h_goal]
    ring_nf
}

lemma ψ_summable (t : ℝ) (ht : t ∈ 𝕋) :
    Summable (fun m => ϕ_term m t) := by
  -- Step 1: Bound the terms of the series
  have h_bound : ∀ m, |ϕ_term m t| ≤ 1 / (8^m) := by
    intro m
    exact ϕ_term_bound m t ht

  -- Step 2: Show that the bounding series is summable
  have h_summable : Summable (fun m => 1 / (8^m : ℝ)) := by
    apply summable_one_div_pow_of_le
    linarith
    exact le_refl

  -- Step 3: Apply the comparison test
  exact Summable.of_norm_bounded _ h_summable h_bound
