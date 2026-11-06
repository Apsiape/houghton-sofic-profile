import Houghton.Analysis.Hamming
import Mathlib.Data.Matrix.Mul

/-!
# Permutation matrices and the normalized Hilbert–Schmidt norm

Bridge between the paper's unitary language and the Hamming language of `PermSectorLemma`:
`σ ↦ P_σ` is multiplicative, and `‖P_σ - P_π‖₂² = τ((P_σ-P_π)ᵀ(P_σ-P_π)) = 2 dH σ π`.
-/

namespace Houghton

open Finset Equiv Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The permutation matrix, `P_σ e_y = e_{σ y}`. -/
def pmat (σ : Perm Ω) : Matrix Ω Ω ℝ := fun x y => if σ y = x then 1 else 0

lemma pmat_mul (σ π : Perm Ω) : pmat σ * pmat π = pmat (σ * π) := by
  ext x y
  simp only [pmat, Matrix.mul_apply, Perm.mul_apply]
  rw [Finset.sum_eq_single (π y)]
  · simp only [ite_true, mul_one]
    exact if_congr Iff.rfl rfl rfl
  · intro z _ hz
    have : ¬ π y = z := fun h => hz h.symm
    simp [this]
  · simp

omit [Fintype Ω] in
lemma pmat_one : pmat (1 : Perm Ω) = 1 := by
  ext x y
  simp only [pmat, Perm.one_apply, Matrix.one_apply]
  by_cases h : y = x
  · simp [h]
  · simp [h, Ne.symm h]

/-- Squared normalized Hilbert–Schmidt norm `‖T‖₂² = D⁻¹ Tr(TᵀT)` of a real matrix. -/
noncomputable def hs2 (T : Matrix Ω Ω ℝ) : ℝ := (∑ x, ∑ y, T x y ^ 2) / Fintype.card Ω

lemma hs2_pmat_sub (σ π : Perm Ω) : hs2 (pmat σ - pmat π) = 2 * dH σ π := by
  have hrow : ∀ y, ∑ x, (pmat σ - pmat π) x y ^ 2 = if σ y ≠ π y then 2 else 0 := by
    intro y
    simp only [Matrix.sub_apply, pmat]
    have e : ∀ x, ((if σ y = x then (1 : ℝ) else 0) - (if π y = x then 1 else 0)) ^ 2 =
        (if σ y = x then 1 else 0) + (if π y = x then 1 else 0) -
          2 * (if σ y = π y then (if σ y = x then 1 else 0) else 0) := by
      intro x
      by_cases h1 : σ y = x <;> by_cases h2 : π y = x
      · simp [h1, h2]; norm_num
      · have : ¬ x = π y := fun h => h2 h.symm
        simp [h1, h2, this]
      · simp [h1, h2]
      · by_cases h3 : σ y = π y <;> simp [h1, h2, h3]
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    by_cases h : σ y = π y
    · simp [h]
      norm_num
    · simp [h]
      norm_num
  unfold hs2
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun y _ => hrow y), Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, dH_eq, hc]
  ring

lemma hs2_pmat_sub_one (σ : Perm Ω) : hs2 (pmat σ - 1) = 2 * dH σ 1 := by
  rw [← pmat_one, hs2_pmat_sub]

lemma hs2_pmat_comm (σ π : Perm Ω) :
    hs2 (pmat σ * pmat π - pmat π * pmat σ) = 2 * dH (σ * π) (π * σ) := by
  rw [pmat_mul, pmat_mul, hs2_pmat_sub]

end Houghton
