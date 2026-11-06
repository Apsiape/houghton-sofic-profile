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
import FiniteLean.QIT.Entropy.Spectral
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

universe u
namespace Houghton
open Finset Equiv Matrix ComplexConjugate
/-! ### Scalar inequalities -/

lemma ent_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    ent x ≤ ent y + (-Real.log y - 1) * (x - y) := by
  unfold ent
  rcases hx.eq_or_lt with h | h
  · subst h; simp; nlinarith [Real.log_le_sub_one_of_pos hy, mul_comm y (Real.log y)]
  · have hl := Real.log_le_sub_one_of_pos (div_pos hy h)
    rw [Real.log_div hy.ne' h.ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl h.le
    have e : x * (y / x - 1) = y - x := by field_simp
    rw [e] at hm
    nlinarith

lemma ent_zero : ent 0 = 0 := by simp [ent]

/-- Jensen for `η` with a doubly stochastic matrix. -/
lemma ent_doubly_stochastic {ι κ : Type*} [Fintype ι] [Fintype κ] (lam : ι → ℝ)
    (B : κ → ι → ℝ) (hlam : ∀ j, 0 ≤ lam j) (hB : ∀ k j, 0 ≤ B k j)
    (hrow : ∀ k, ∑ j, B k j = 1) (hcol : ∀ j, ∑ k, B k j = 1) :
    ∑ j, ent (lam j) ≤ ∑ k, ent (∑ j, B k j * lam j) := by
  have hk : ∀ k, ∑ j, B k j * ent (lam j) ≤ ent (∑ j, B k j * lam j) := by
    intro k
    set d := ∑ j, B k j * lam j with hd
    have hd0 : 0 ≤ d := sum_nonneg fun j _ => mul_nonneg (hB k j) (hlam j)
    rcases hd0.eq_or_lt with h0 | hpos
    · have hz : ∀ j, B k j * lam j = 0 := by
        intro j
        have := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hB k j) (hlam j))).mp h0.symm j
          (mem_univ j)
        exact this
      rw [← h0, ent_zero]
      apply le_of_eq
      refine sum_eq_zero fun j _ => ?_
      rcases mul_eq_zero.mp (hz j) with h | h
      · rw [h, zero_mul]
      · rw [h, ent_zero, mul_zero]
    · calc ∑ j, B k j * ent (lam j)
          ≤ ∑ j, B k j * (ent d + (-Real.log d - 1) * (lam j - d)) :=
            sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ent_tangent (hlam j) hpos) (hB k j)
        _ = ∑ j, (ent d * B k j + (-Real.log d - 1) * (B k j * lam j) -
              (-Real.log d - 1) * d * B k j) := sum_congr rfl fun j _ => by ring
        _ = ent d * ∑ j, B k j + (-Real.log d - 1) * (∑ j, B k j * lam j) -
              (-Real.log d - 1) * d * ∑ j, B k j := by
            rw [sum_sub_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
        _ = ent d := by rw [hrow k, ← hd]; ring
  calc ∑ j, ent (lam j) = ∑ j, (∑ k, B k j) * ent (lam j) := by simp [hcol]
    _ = ∑ k, ∑ j, B k j * ent (lam j) := by
        simp only [sum_mul]; rw [sum_comm]
    _ ≤ _ := sum_le_sum fun k _ => hk k

/-- `∑_{k ∈ S} η(xₖ) ≤ η(s) + s log m` when `|S| ≤ m` and `∑_{k∈S} xₖ = s`. -/
lemma ent_group_le {κ : Type*} (S : Finset κ) (x : κ → ℝ) (m : ℕ) (hm : 0 < m)
    (hS : S.card ≤ m) (hx : ∀ k ∈ S, 0 ≤ x k) :
    ∑ k ∈ S, ent (x k) ≤ ent (∑ k ∈ S, x k) + (∑ k ∈ S, x k) * Real.log m := by
  set s := ∑ k ∈ S, x k with hs
  have hs0 : 0 ≤ s := sum_nonneg hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases hs0.eq_or_lt with h0 | hpos
  · have hz : ∀ k ∈ S, x k = 0 := fun k hk => (sum_eq_zero_iff_of_nonneg hx).mp h0.symm k hk
    rw [← h0, ent_zero, zero_mul, add_zero]
    apply le_of_eq
    exact sum_eq_zero fun k hk => by rw [hz k hk, ent_zero]
  · set y := s / m with hy
    have hypos : 0 < y := div_pos hpos hmR
    have hcard : (S.card : ℝ) ≤ m := by exact_mod_cast hS
    calc ∑ k ∈ S, ent (x k) ≤ ∑ k ∈ S, (ent y + (-Real.log y - 1) * (x k - y)) :=
          sum_le_sum fun k hk => ent_tangent (hx k hk) hypos
      _ = S.card * ent y + (-Real.log y - 1) * (s - S.card * y) := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, sum_sub_distrib, sum_const,
            nsmul_eq_mul]
      _ = s * (-Real.log y) - s + S.card * y := by unfold ent; ring
      _ ≤ s * (-Real.log y) := by
          have : (S.card : ℝ) * y ≤ s := by
            rw [hy, ← mul_div_assoc, div_le_iff₀ hmR]; nlinarith
          linarith
      _ = ent s + s * Real.log m := by
          unfold ent
          rw [hy, Real.log_div hpos.ne' hmR.ne']
          ring

/-! ### Matrix lemmas -/

section MatGen

variable {n : Type u} [Fintype n] [DecidableEq n]

lemma col_normSq_of_unitary (W : Matrix n n ℂ) (h : Wᴴ * W = 1) (k : n) :
    ∑ p, Complex.normSq (W p k) = 1 := by
  have h1 := congrFun (congrFun h k) k
  rw [mul_apply, one_apply_eq] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  refine sum_congr rfl fun p _ => ?_
  rw [conjTranspose_apply, show star (W p k) = conj (W p k) from rfl,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

lemma row_normSq_of_unitary (V : Matrix n n ℂ) (h : V * Vᴴ = 1) (j : n) :
    ∑ k, Complex.normSq (V j k) = 1 := by
  have h1 := congrFun (congrFun h j) j
  rw [mul_apply, one_apply_eq] at h1
  have h2 := congrArg Complex.re h1
  rw [Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  refine sum_congr rfl fun k _ => ?_
  rw [conjTranspose_apply, show star (V j k) = conj (V j k) from rfl, Complex.mul_conj,
    Complex.ofReal_re]

/-- Schur–Jensen: `S(A) ≤ ∑ₖ η(⟨wₖ, A wₖ⟩)` for every orthonormal basis (columns of a unitary `W`). -/
lemma vN_le_diag {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpsd : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re)
    (W : Matrix n n ℂ) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1) :
    vN A ≤ ∑ k, ent ((star (fun p => W p k) ⬝ᵥ (A *ᵥ fun p => W p k)).re) := by
  rw [vN_eq hA]
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : U * Uᴴ = 1 := by
    rw [hU, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hUU' : Uᴴ * U = 1 := by
    rw [hU, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self]
  set B : n → n → ℝ := fun k j => Complex.normSq ((Uᴴ * W) j k) with hB
  have hd : ∀ k, (star (fun p => W p k) ⬝ᵥ (A *ᵥ fun p => W p k)).re =
      ∑ j, B k j * hA.eigenvalues j := by
    intro k
    rw [re_dot_herm hA]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_comm, hB]
    congr 2
  simp only [hd]
  refine ent_doubly_stochastic _ B (eig_nonneg_of_psd hA hpsd)
    (fun k j => Complex.normSq_nonneg _) (fun k => ?_) (fun j => ?_)
  · -- row sums: `‖Uᴴ wₖ‖² = ‖wₖ‖² = 1`
    have h1 := col_normSq_of_unitary (Uᴴ * W) (by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc U, hUU, Matrix.one_mul, hW2]) k
    exact h1
  · exact row_normSq_of_unitary (Uᴴ * W) (by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc W, hW1, Matrix.one_mul, hUU']) j

lemma rank_add_le' (A B : Matrix n n ℂ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ↥((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule ℂ (n → ℂ))) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- A Hermitian idempotent of trace `D` has rank `D`. -/
lemma rank_proj {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (D : ℕ)
    (htr : P.trace = D) : P.rank = D := by
  have hH : P.IsHermitian := hP
  have h01 : ∀ j, hH.eigenvalues j = 0 ∨ hH.eigenvalues j = 1 := by
    intro j
    have hev := hH.mulVec_eigenvectorBasis j
    have h2 : P *ᵥ (P *ᵥ ⇑(hH.eigenvectorBasis j)) = P *ᵥ ⇑(hH.eigenvectorBasis j) := by
      rw [mulVec_mulVec, hPP]
    rw [hev, mulVec_smul, hev, smul_smul] at h2
    have hne : (⇑(hH.eigenvectorBasis j) : n → ℂ) ≠ 0 := by
      intro h0
      have := hH.eigenvectorBasis.orthonormal.1 j
      have h0' : hH.eigenvectorBasis j = 0 := by
        ext i; simpa using congrFun h0 i
      rw [h0', norm_zero] at this
      exact zero_ne_one this
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have h3 := congrFun h2 i
    simp only [Pi.smul_apply, Complex.real_smul] at h3
    have hi' : (hH.eigenvectorBasis j) i ≠ 0 := hi
    have h4 := mul_right_cancel₀ hi' h3
    have hl' : hH.eigenvalues j * hH.eigenvalues j = hH.eigenvalues j := by
      have h5 : ((hH.eigenvalues j * hH.eigenvalues j : ℝ) : ℂ) = ((hH.eigenvalues j : ℝ) : ℂ) := by
        simpa using h4
      exact Complex.ofReal_injective h5
    rcases mul_eq_zero.mp (show hH.eigenvalues j * (hH.eigenvalues j - 1) = 0 by linarith) with
      h | h
    · left; exact h
    · right; linarith
  have hsum := hH.trace_eq_sum_eigenvalues
  rw [htr] at hsum
  have hsumR : (D : ℝ) = ∑ j, hH.eigenvalues j := by
    have h := congrArg Complex.re hsum
    rw [Complex.natCast_re, Complex.re_sum] at h
    simpa using h
  rw [hH.rank_eq_card_non_zero_eigs]
  have hcard : (Fintype.card {i // hH.eigenvalues i ≠ 0} : ℝ) = ∑ j, hH.eigenvalues j := by
    rw [Fintype.card_subtype, card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    rcases h01 j with h | h <;> simp [h]
  exact_mod_cast hcard.trans hsumR.symm

lemma conj_quad (Z X : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((Z * X * Zᴴ) *ᵥ v) = star (Zᴴ *ᵥ v) ⬝ᵥ (X *ᵥ (Zᴴ *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
    conjTranspose_conjTranspose]

lemma normSq_conjT_unitary (Z : Matrix n n ℂ) (hZ : Z * Zᴴ = 1) (v : n → ℂ) :
    ∑ j, Complex.normSq ((Zᴴ *ᵥ v) j) = ∑ j, Complex.normSq (v j) := by
  rw [← dot_star_self_re, ← dot_star_self_re, star_mulVec, conjTranspose_conjTranspose,
    ← dotProduct_mulVec, mulVec_mulVec, hZ, one_mulVec]

lemma proj_eig01 {P : Matrix n n ℂ} (hH : P.IsHermitian) (hPP : P * P = P) (j : n) :
    hH.eigenvalues j = 0 ∨ hH.eigenvalues j = 1 := by
  have hev := hH.mulVec_eigenvectorBasis j
  have h2 : P *ᵥ (P *ᵥ ⇑(hH.eigenvectorBasis j)) = P *ᵥ ⇑(hH.eigenvectorBasis j) := by
    rw [mulVec_mulVec, hPP]
  rw [hev, mulVec_smul, hev, smul_smul] at h2
  have hne : (⇑(hH.eigenvectorBasis j) : n → ℂ) ≠ 0 := by
    intro h0
    have := hH.eigenvectorBasis.orthonormal.1 j
    have h0' : hH.eigenvectorBasis j = 0 := by
      ext i; simpa using congrFun h0 i
    rw [h0', norm_zero] at this
    exact zero_ne_one this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have h3 := congrFun h2 i
  simp only [Pi.smul_apply, Complex.real_smul] at h3
  have hi' : (hH.eigenvectorBasis j) i ≠ 0 := hi
  have h4 := mul_right_cancel₀ hi' h3
  have hl' : hH.eigenvalues j * hH.eigenvalues j = hH.eigenvalues j := by
    have h5 : ((hH.eigenvalues j * hH.eigenvalues j : ℝ) : ℂ) = ((hH.eigenvalues j : ℝ) : ℂ) := by
      simpa using h4
    exact Complex.ofReal_injective h5
  rcases mul_eq_zero.mp (show hH.eigenvalues j * (hH.eigenvalues j - 1) = 0 by linarith) with
    h | h
  · left; exact h
  · right; linarith

lemma proj_quad_bounds {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (v : n → ℂ) :
    0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re ∧ (star v ⬝ᵥ (P *ᵥ v)).re ≤ ∑ j, Complex.normSq (v j) := by
  have hH : P.IsHermitian := hP
  rw [re_dot_herm hH, ← sum_normSq_star_unitary hH v]
  constructor
  · exact sum_nonneg fun j _ => by
      rcases proj_eig01 hH hPP j with h | h <;> rw [h] <;> simp [Complex.normSq_nonneg]
  · exact sum_le_sum fun j _ => by
      rcases proj_eig01 hH hPP j with h | h <;> rw [h] <;> simp [Complex.normSq_nonneg]

lemma sum_quad_eq_trace (W X : Matrix n n ℂ) (hW : W * Wᴴ = 1) :
    ∑ k, star (fun p => W p k) ⬝ᵥ (X *ᵥ fun p => W p k) = X.trace := by
  have e : ∀ k, star (fun p => W p k) ⬝ᵥ (X *ᵥ fun p => W p k) = (Wᴴ * X * W) k k := by
    intro k
    simp only [dotProduct, mulVec, mul_apply, conjTranspose_apply, Pi.star_apply, mul_sum,
      sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun q _ => sum_congr rfl fun p _ => by ring
  rw [sum_congr rfl fun k _ => e k]
  change (Wᴴ * X * W).trace = X.trace
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one]

lemma eq_zero_of_normSq_sum (v : n → ℂ) (h : ∑ j, Complex.normSq (v j) ≤ 0) : v = 0 := by
  funext j
  have h0 : ∑ j, Complex.normSq (v j) = 0 :=
    le_antisymm h (sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  have := (sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (v j))).mp h0 j (mem_univ j)
  simpa using this

end MatGen

lemma dot_proj {n : Type u} [Fintype n] [DecidableEq n] (R : Matrix n n ℂ) (hR : Rᴴ = R)
    (hRR : R * R = R) (b : n → ℂ) : star b ⬝ᵥ (R *ᵥ b) = star (R *ᵥ b) ⬝ᵥ (R *ᵥ b) := by
  calc star b ⬝ᵥ (R *ᵥ b) = star b ⬝ᵥ ((R * R) *ᵥ b) := by rw [hRR]
    _ = star b ⬝ᵥ (R *ᵥ (R *ᵥ b)) := by rw [mulVec_mulVec]
    _ = (star b ᵥ* R) ⬝ᵥ (R *ᵥ b) := dotProduct_mulVec _ _ _
    _ = star (R *ᵥ b) ⬝ᵥ (R *ᵥ b) := by rw [star_mulVec, hR]

/-- Structure of the adapted eigenbasis: every eigenvector of `M = 3P + (1-P)Q(1-P)` lies in
`ran P` or in `ker P` when `⟨v, Q v⟩ ≤ 2‖v‖²`. -/
lemma adapted_eigvec {n : Type u} [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ) (hP : Pᴴ = P)
    (hPP : P * P = P) (hQ : ∀ v : n → ℂ, (star v ⬝ᵥ (Q *ᵥ v)).re ≤ 2 * ∑ j, Complex.normSq (v j))
    (b : n → ℂ) (μ : ℝ)
    (hb : ((3 : ℂ) • P + (1 - P) * Q * (1 - P)) *ᵥ b = μ • b) :
    P *ᵥ b = b ∨ P *ᵥ b = 0 := by
  have hPmul : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hmulP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have h1P : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.mul_sub, Matrix.mul_one, hmulP, sub_zero]
  have h1H : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hP]
  have hPM : P * ((3 : ℂ) • P + (1 - P) * Q * (1 - P)) = (3 : ℂ) • P := by
    rw [Matrix.mul_add, Matrix.mul_smul, hPP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPmul,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  have hPb : ((3 : ℝ) : ℂ) • (P *ᵥ b) = (μ : ℂ) • (P *ᵥ b) := by
    have := congrArg (fun v => P *ᵥ v) hb
    simp only [mulVec_mulVec, hPM, smul_mulVec, mulVec_smul] at this
    funext j
    have hj := congrFun this j
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul] at hj ⊢
    push_cast
    exact hj
  by_cases hμ : μ = 3
  · left
    have h1M : (1 - P) * ((3 : ℂ) • P + (1 - P) * Q * (1 - P)) = (1 - P) * Q * (1 - P) := by
      rw [Matrix.mul_add, Matrix.mul_smul, hmulP, smul_zero, zero_add, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, h1P]
    have hK : ((1 - P) * Q * (1 - P)) *ᵥ b = μ • ((1 - P) *ᵥ b) := by
      have := congrArg (fun v => (1 - P) *ᵥ v) hb
      simp only [mulVec_mulVec, h1M] at this
      rw [this, mulVec_smul]
    set v := (1 - P) *ᵥ b with hv
    have hq : (star v ⬝ᵥ (Q *ᵥ v)).re = μ * ∑ j, Complex.normSq (v j) := by
      have e : star v ⬝ᵥ (Q *ᵥ v) = star b ⬝ᵥ (((1 - P) * Q * (1 - P)) *ᵥ b) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hv, star_mulVec, h1H]
        simp only [dotProduct_mulVec]
      rw [e, hK, dotProduct_smul, dot_proj (1 - P) h1H h1P b, ← hv, Complex.real_smul,
        Complex.re_ofReal_mul, dot_star_self_re]
    have := hQ v
    rw [hq, hμ] at this
    have hv0 : v = 0 := eq_zero_of_normSq_sum v (by linarith)
    have : b - P *ᵥ b = 0 := by rw [← hv0, hv, sub_mulVec, one_mulVec]
    exact (sub_eq_zero.mp this).symm
  · right
    have h3 : (((3 : ℝ) : ℂ) - μ) • (P *ᵥ b) = 0 := by rw [sub_smul, hPb, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd (by exact_mod_cast (sub_eq_zero.mp h).symm) hμ
    · exact h

lemma vN_le_diag_b {n : Type u} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hpsd : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re)
    (W : Matrix n n ℂ) (hW1 : W * Wᴴ = 1) (hW2 : Wᴴ * W = 1) (b : n → n → ℂ)
    (hb : ∀ k p, b k p = W p k) :
    vN A ≤ ∑ k, ent ((star (b k) ⬝ᵥ (A *ᵥ b k)).re) := by
  have : b = fun k p => W p k := funext fun k => funext fun p => hb k p
  subst this
  exact vN_le_diag hA hpsd W hW1 hW2

lemma sum_quad_eq_trace_b {n : Type u} [Fintype n] [DecidableEq n] (W X : Matrix n n ℂ)
    (hW : W * Wᴴ = 1) (b : n → n → ℂ) (hb : ∀ k p, b k p = W p k) :
    ∑ k, star (b k) ⬝ᵥ (X *ᵥ b k) = X.trace := by
  have : b = fun k p => W p k := funext fun k => funext fun p => hb k p
  subst this
  exact sum_quad_eq_trace W X hW

lemma rank_conj_le {n : Type u} [Fintype n] [DecidableEq n] (Z X : Matrix n n ℂ) :
    (Z * X * Zᴴ).rank ≤ X.rank :=
  (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)


end Houghton
