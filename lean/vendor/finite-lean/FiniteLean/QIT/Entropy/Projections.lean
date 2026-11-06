import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lemma `lem:projections` (projection products)

For orthogonal projections `P₁, …, P_m` on a real inner product space,
`‖x‖² - ⟪x, P_m ⋯ P₁ x⟫ ≤ 2 ∑ⱼ ‖(I - Pⱼ) x‖²`.  For `‖x‖ = 1` this is the paper's
`1 - Re⟨x, P_m ⋯ P₁ x⟩ ≤ 2 ∑ⱼ ‖(I - Pⱼ)x‖²` (a complex Hilbert space is a real inner product
space for `Re⟨·,·⟩`, with the same orthogonal projections).  This is an analytic input of
Lemma `lem:sector` and Theorem `thm:phase-robust`; it is not used by the reduction files.
-/

namespace Houghton

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `P` is an orthogonal projection: an idempotent symmetric linear map. -/
structure IsOrthProj (P : E →ₗ[ℝ] E) : Prop where
  idem : ∀ x, P (P x) = P x
  symm : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)

namespace IsOrthProj

variable {P : E →ₗ[ℝ] E} (hP : IsOrthProj P)
include hP

lemma inner_range_ker (x y : E) : inner ℝ (P x) (y - P y) = 0 := by
  rw [inner_sub_right, hP.symm x y, hP.symm x (P y), hP.idem, sub_self]

lemma inner_eq_inner_sub (x z : E) : inner ℝ x (z - P z) = inner ℝ (x - P x) (z - P z) := by
  rw [inner_sub_left, hP.inner_range_ker, sub_zero]

lemma norm_sq_split (z : E) : ‖z‖ ^ 2 = ‖P z‖ ^ 2 + ‖z - P z‖ ^ 2 := by
  have h := norm_add_sq_real (P z) (z - P z)
  rw [hP.inner_range_ker, mul_zero, add_zero, add_sub_cancel] at h
  exact h

end IsOrthProj

/-- `iterProj P x m = P_{m-1} (⋯ (P_0 x))`. -/
def iterProj (P : ℕ → E →ₗ[ℝ] E) (x : E) : ℕ → E
  | 0 => x
  | j + 1 => P j (iterProj P x j)

/-- **Lemma `lem:projections`**, homogeneous form. -/
theorem projection_products (P : ℕ → E →ₗ[ℝ] E) (hP : ∀ j, IsOrthProj (P j)) (x : E) (m : ℕ) :
    ‖x‖ ^ 2 - inner ℝ x (iterProj P x m) ≤ 2 * ∑ j ∈ range m, ‖x - P j x‖ ^ 2 := by
  set y := iterProj P x with hy
  have hy0 : y 0 = x := rfl
  have hys : ∀ j, y (j + 1) = P j (y j) := fun j => rfl
  -- `b = ∑ ‖r_j‖² = ‖x‖² - ‖x_m‖²`
  have hb : ∑ j ∈ range m, ‖y j - y (j + 1)‖ ^ 2 = ‖x‖ ^ 2 - ‖y m‖ ^ 2 := by
    have step : ∀ j, ‖y j - y (j + 1)‖ ^ 2 = ‖y j‖ ^ 2 - ‖y (j + 1)‖ ^ 2 := by
      intro j
      have := (hP j).norm_sq_split (y j)
      rw [hys]
      linarith
    rw [sum_congr rfl (fun j _ => step j), sum_range_sub' (fun j => ‖y j‖ ^ 2), hy0]
  -- `a = ‖x‖² - ⟪x, x_m⟫ = ∑ ⟪(I - P_j) x, r_j⟫`
  have ha : ‖x‖ ^ 2 - inner ℝ x (y m) =
      ∑ j ∈ range m, inner ℝ (x - P j x) (y j - y (j + 1)) := by
    have step : ∀ j, inner ℝ (x - P j x) (y j - y (j + 1)) =
        inner ℝ x (y j) - inner ℝ x (y (j + 1)) := by
      intro j
      rw [hys, ← (hP j).inner_eq_inner_sub x (y j), inner_sub_right]
    rw [sum_congr rfl (fun j _ => step j), sum_range_sub' (fun j => inner ℝ x (y j)), hy0,
      real_inner_self_eq_norm_sq]
  -- Cauchy–Schwarz: `a² ≤ E b`
  set a := ‖x‖ ^ 2 - inner ℝ x (y m) with hadef
  set Es := ∑ j ∈ range m, ‖x - P j x‖ ^ 2 with hEs
  have hEs0 : 0 ≤ Es := sum_nonneg (fun j _ => sq_nonneg _)
  have hcs : a ^ 2 ≤ Es * (‖x‖ ^ 2 - ‖y m‖ ^ 2) := by
    rw [ha, ← hb]
    have h1 : |∑ j ∈ range m, inner ℝ (x - P j x) (y j - y (j + 1))| ≤
        ∑ j ∈ range m, ‖x - P j x‖ * ‖y j - y (j + 1)‖ :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => abs_real_inner_le_norm _ _))
    have h2 := sum_mul_sq_le_sq_mul_sq (range m) (fun j => ‖x - P j x‖)
      (fun j => ‖y j - y (j + 1)‖)
    have h3 : (∑ j ∈ range m, inner ℝ (x - P j x) (y j - y (j + 1))) ^ 2 ≤
        (∑ j ∈ range m, ‖x - P j x‖ * ‖y j - y (j + 1)‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact h3.trans h2
  -- `0 ≤ ‖x - x_m‖² = 2a - b`
  have hab : ‖x‖ ^ 2 - ‖y m‖ ^ 2 ≤ 2 * a := by
    have h := norm_sub_sq_real x (y m)
    have h0 := sq_nonneg ‖x - y m‖
    rw [hadef]
    linarith
  -- conclude `a ≤ 2E`
  by_cases hpos : a ≤ 0
  · linarith
  · push Not at hpos
    have : a ^ 2 ≤ Es * (2 * a) := hcs.trans (mul_le_mul_of_nonneg_left hab hEs0)
    nlinarith

/-- **Lemma `lem:projections`**: for a unit vector, `1 - ⟪x, P_m ⋯ P₁ x⟫ ≤ 2 ∑ ‖(I - P_j)x‖²`. -/
theorem projection_products_unit (P : ℕ → E →ₗ[ℝ] E) (hP : ∀ j, IsOrthProj (P j)) (x : E)
    (hx : ‖x‖ = 1) (m : ℕ) :
    1 - inner ℝ x (iterProj P x m) ≤ 2 * ∑ j ∈ range m, ‖x - P j x‖ ^ 2 := by
  have := projection_products P hP x m
  rwa [hx, one_pow] at this

end Houghton
