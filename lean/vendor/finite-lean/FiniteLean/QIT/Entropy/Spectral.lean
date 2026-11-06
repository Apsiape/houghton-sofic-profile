import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Analysis.Matrix.Spectrum
import FiniteLean.QIT.Entropy.Basic

universe u
namespace Houghton
open Finset Equiv Matrix ComplexConjugate
section Spec

variable {n : Type u} [Fintype n] [DecidableEq n]

lemma dot_star_self_re (w : n → ℂ) : (star w ⬝ᵥ w).re = ∑ j, Complex.normSq (w j) := by
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [show star (w j) = conj (w j) from rfl, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma re_dot_le (a b : n → ℂ) :
    (star a ⬝ᵥ b).re ≤ Real.sqrt (∑ j, Complex.normSq (a j)) * Real.sqrt (∑ j, Complex.normSq (b j)) := by
  have h1 : (star a ⬝ᵥ b).re ≤ ∑ j, ‖a j‖ * ‖b j‖ := by
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine sum_le_sum fun j _ => (Complex.re_le_norm _).trans ?_
    rw [norm_mul, show star (a j) = conj (a j) from rfl, Complex.norm_conj]
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun j => ‖a j‖) (fun j => ‖b j‖)
  simp only [← Complex.normSq_eq_norm_sq] at h2
  linarith

lemma herm_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j => (hA.eigenvalues j : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hA.spectral_theorem]
  rfl

/-- `⟨v, A v⟩ = ∑ⱼ λⱼ |(U* v)ⱼ|²`. -/
lemma re_dot_herm {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    (star v ⬝ᵥ (A *ᵥ v)).re = ∑ j, hA.eigenvalues j *
      Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ v) j) := by
  have e : star v ⬝ᵥ (A *ᵥ v) =
      star (star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ v) ⬝ᵥ
        (diagonal (fun j => (hA.eigenvalues j : ℂ)) *ᵥ
          (star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ v)) := by
    conv_lhs => rw [herm_decomp hA]
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    congr 1
    rw [star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [e]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul,
    show star ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ v) j) =
      conj ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ v) j) from rfl,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma sum_normSq_star_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) (v : n → ℂ) :
    ∑ j, Complex.normSq ((star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ v) j) =
      ∑ j, Complex.normSq (v j) := by
  rw [← dot_star_self_re, ← dot_star_self_re, star_mulVec, Matrix.star_eq_conjTranspose,
    conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec,
    ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.coe_mul_star_self, one_mulVec]

lemma eig_le_of_cap {A : Matrix n n ℂ} (hA : A.IsHermitian) (κ : ℝ)
    (hcap : ∀ v : n → ℂ, (star v ⬝ᵥ (A *ᵥ v)).re ≤ κ * ∑ j, Complex.normSq (v j)) (j : n) :
    hA.eigenvalues j ≤ κ := by
  have h := hcap ⇑(hA.eigenvectorBasis j)
  have he : (star ⇑(hA.eigenvectorBasis j) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis j))).re =
      hA.eigenvalues j := (hA.eigenvalues_eq j).symm
  rw [he] at h
  have hn : ∑ i, Complex.normSq ((hA.eigenvectorBasis j) i) = 1 := by
    have h1 := hA.eigenvectorBasis.orthonormal.1 j
    rw [EuclideanSpace.norm_eq] at h1
    have h2 : (∑ i, ‖(hA.eigenvectorBasis j) i‖ ^ 2) = 1 := by
      have := congrArg (· ^ 2) h1
      simp only [one_pow] at this
      rwa [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at this
    simpa [Complex.normSq_eq_norm_sq] using h2
  rw [hn, mul_one] at h
  exact h

lemma eig_nonneg_of_psd {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpsd : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re) (j : n) : 0 ≤ hA.eigenvalues j := by
  rw [hA.eigenvalues_eq]; exact hpsd _

lemma sum_eig_of_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) (htr : A.trace = 1) :
    ∑ j, hA.eigenvalues j = 1 := by
  have h := hA.trace_eq_sum_eigenvalues
  rw [htr] at h
  have : ((∑ j, hA.eigenvalues j : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    push_cast; rw [h]; rfl
  exact_mod_cast this

lemma vN_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) : vN A = ∑ j, ent (hA.eigenvalues j) := by
  unfold vN
  rw [dif_pos hA]

/-- If a density matrix has all eigenvalues `≤ 1/D` then `S ≥ log D`. -/
lemma log_le_vN_of_cap {A : Matrix n n ℂ} (hA : IsDensity A) (D : ℝ) (hD : 0 < D)
    (hcap : ∀ v : n → ℂ, (star v ⬝ᵥ (A *ᵥ v)).re ≤ D⁻¹ * ∑ j, Complex.normSq (v j)) :
    Real.log D ≤ vN A := by
  obtain ⟨hH, hpsd, htr⟩ := hA
  rw [vN_eq hH]
  have hsum := sum_eig_of_trace hH htr
  calc Real.log D = ∑ j, hH.eigenvalues j * Real.log D := by rw [← sum_mul, hsum, one_mul]
    _ ≤ ∑ j, ent (hH.eigenvalues j) := sum_le_sum fun j _ => by
        have h0 := eig_nonneg_of_psd hH hpsd j
        have h1 := eig_le_of_cap hH D⁻¹ hcap j
        rcases h0.eq_or_lt with h | h
        · rw [← h]; simp [ent]
        · unfold ent
          have hinv : D ≤ (hH.eigenvalues j)⁻¹ := by rw [le_inv_comm₀ hD h]; exact h1
          have : Real.log D ≤ -Real.log (hH.eigenvalues j) := by
            rw [← Real.log_inv]
            exact Real.log_le_log hD hinv
          nlinarith

end Spec

section Spec2

variable {n : Type u} [Fintype n] [DecidableEq n]

lemma eigvec_normSq_sum {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : n) :
    ∑ i, Complex.normSq ((hA.eigenvectorUnitary : Matrix n n ℂ) i j) = 1 := by
  have h1 := hA.eigenvectorBasis.orthonormal.1 j
  rw [EuclideanSpace.norm_eq] at h1
  have h2 : (∑ i, ‖(hA.eigenvectorBasis j) i‖ ^ 2) = 1 := by
    have := congrArg (· ^ 2) h1
    simp only [one_pow] at this
    rwa [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at this
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  simpa [Complex.normSq_eq_norm_sq] using h2

lemma herm_diag_re {A : Matrix n n ℂ} (hA : A.IsHermitian) (p : n) :
    (A p p).re = ∑ j, hA.eigenvalues j *
      Complex.normSq ((hA.eigenvectorUnitary : Matrix n n ℂ) p j) := by
  conv_lhs => rw [herm_decomp hA]
  simp only [mul_apply, diagonal, of_apply, Matrix.star_apply, mul_ite, mul_zero, sum_ite_eq',
    mem_univ, if_true, Complex.re_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_right_comm, show star ((hA.eigenvectorUnitary : Matrix n n ℂ) p j) =
      conj ((hA.eigenvectorUnitary : Matrix n n ℂ) p j) from rfl, Complex.mul_conj,
    ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]

lemma eigvec_mulVec {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : n) :
    A *ᵥ (fun p => (hA.eigenvectorUnitary : Matrix n n ℂ) p j) =
      (hA.eigenvalues j : ℂ) • (fun p => (hA.eigenvectorUnitary : Matrix n n ℂ) p j) := by
  have := hA.mulVec_eigenvectorBasis j
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  rw [this]
  funext p
  simp [Pi.smul_apply, Complex.real_smul]

lemma normSq_dot_le (a b : n → ℂ) :
    Complex.normSq (star a ⬝ᵥ b) ≤ (∑ j, Complex.normSq (a j)) * ∑ j, Complex.normSq (b j) := by
  have h1 : ‖star a ⬝ᵥ b‖ ≤ ∑ j, ‖a j‖ * ‖b j‖ := by
    simp only [dotProduct, Pi.star_apply]
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
    rw [norm_mul, show star (a j) = conj (a j) from rfl, Complex.norm_conj]
  have h2 := sum_mul_sq_le_sq_mul_sq univ (fun j => ‖a j‖) (fun j => ‖b j‖)
  rw [Complex.normSq_eq_norm_sq]
  simp only [← Complex.normSq_eq_norm_sq] at h2
  calc ‖star a ⬝ᵥ b‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end Spec2


end Houghton
