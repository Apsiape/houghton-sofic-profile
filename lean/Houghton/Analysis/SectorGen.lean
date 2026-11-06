import FiniteLean.QIT.Entropy.MatrixBounds
import Houghton.Analysis.SectorTwirl
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Proof of the generic single-twirl bound `GenTwirlBound`

Elementary finite-dimensional matrix analysis: the tangent-line inequality for `η(x) = -x log x`,
the Schur–Jensen bound `S(σ) ≤ ∑ₖ η(⟨bₖ, σ bₖ⟩)` for every orthonormal basis, an eigenbasis adapted
to `ran P ⊕ ker P`, and rank counting.
-/

universe u

namespace Houghton

open Finset Equiv Matrix ComplexConjugate

theorem genTwirlBound : GenTwirlBound.{u} := by
  intro n _ _ P Z₁ Z₂ D w hP hPP htr hD hZ1 hZ2 hw0 hw
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hZ1' : Z₁ᴴ * Z₁ = 1 := mul_eq_one_comm.mp hZ1
  have hZ2' : Z₂ᴴ * Z₂ = 1 := mul_eq_one_comm.mp hZ2
  obtain ⟨P₁, hP₁⟩ : ∃ X : Matrix n n ℂ, X = Z₁ * P * Z₁ᴴ := ⟨_, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ X : Matrix n n ℂ, X = Z₂ * P * Z₂ᴴ := ⟨_, rfl⟩
  rw [← hP₁, ← hP₂] at hw0 ⊢
  set c : ℝ := (3 * (D : ℝ))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hs : (((3 * D : ℕ) : ℂ))⁻¹ = (c : ℂ) := by rw [hc]; push_cast; ring
  rw [hs] at hw0 ⊢
  obtain ⟨σ, hσ⟩ : ∃ X : Matrix n n ℂ, X = (c : ℂ) • (P + P₁ + P₂) := ⟨_, rfl⟩
  rw [← hσ] at hw0 ⊢
  -- projections
  have hPtH : ∀ Z : Matrix n n ℂ, (Z * P * Zᴴ)ᴴ = Z * P * Zᴴ := by
    intro Z
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]
  have hP₁H : P₁ᴴ = P₁ := by rw [hP₁, hPtH]
  have hP₂H : P₂ᴴ = P₂ := by rw [hP₂, hPtH]
  have hqt : ∀ Z : Matrix n n ℂ, Z * Zᴴ = 1 → ∀ v : n → ℂ,
      0 ≤ (star v ⬝ᵥ ((Z * P * Zᴴ) *ᵥ v)).re ∧
        (star v ⬝ᵥ ((Z * P * Zᴴ) *ᵥ v)).re ≤ ∑ j, Complex.normSq (v j) := by
    intro Z hZ v
    rw [conj_quad, ← normSq_conjT_unitary Z hZ v]
    exact proj_quad_bounds hP hPP _
  have hq1 : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (P₁ *ᵥ v)).re ∧
      (star v ⬝ᵥ (P₁ *ᵥ v)).re ≤ ∑ j, Complex.normSq (v j) := by rw [hP₁]; exact hqt Z₁ hZ1
  have hq2 : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (P₂ *ᵥ v)).re ∧
      (star v ⬝ᵥ (P₂ *ᵥ v)).re ≤ ∑ j, Complex.normSq (v j) := by rw [hP₂]; exact hqt Z₂ hZ2
  have hq0 := fun v => proj_quad_bounds hP hPP v
  have hqσ : ∀ v : n → ℂ, (star v ⬝ᵥ (σ *ᵥ v)).re = c * ((star v ⬝ᵥ (P *ᵥ v)).re +
      (star v ⬝ᵥ (P₁ *ᵥ v)).re + (star v ⬝ᵥ (P₂ *ᵥ v)).re) := by
    intro v
    rw [hσ, smul_mulVec, add_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dotProduct_add,
      smul_eq_mul, Complex.re_ofReal_mul, Complex.add_re, Complex.add_re]
  have hσH : σ.IsHermitian := by
    unfold IsHermitian
    rw [hσ, conjTranspose_smul, conjTranspose_add, conjTranspose_add, hP, hP₁H, hP₂H]
    congr 1
    simp
  have hσpsd : ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (σ *ᵥ v)).re := by
    intro v
    rw [hqσ]
    exact mul_nonneg hc0.le (by linarith [(hq0 v).1, (hq1 v).1, (hq2 v).1])
  have htrt : ∀ Z : Matrix n n ℂ, Zᴴ * Z = 1 → (Z * P * Zᴴ).trace = D := by
    intro Z hZ
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hZ, Matrix.mul_one, htr]
  have hσtr : σ.trace.re = 1 := by
    rw [hσ, trace_smul, trace_add, trace_add, htr, hP₁, htrt Z₁ hZ1', hP₂, htrt Z₂ hZ2',
      smul_eq_mul, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.natCast_re]
    rw [hc]
    field_simp
    ring
  -- the adapted eigenbasis
  set Q := P₁ + P₂ with hQdef
  have hQ : ∀ v : n → ℂ, (star v ⬝ᵥ (Q *ᵥ v)).re ≤ 2 * ∑ j, Complex.normSq (v j) := by
    intro v
    rw [hQdef, add_mulVec, dotProduct_add, Complex.add_re]
    linarith [(hq1 v).2, (hq2 v).2]
  set M := (3 : ℂ) • P + (1 - P) * Q * (1 - P) with hMdef
  have h1H : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hP]
  have hMH : M.IsHermitian := by
    unfold IsHermitian
    rw [hMdef, conjTranspose_add, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, h1H,
      hQdef, conjTranspose_add, hP₁H, hP₂H, hP, Matrix.mul_assoc]
    congr 1
    simp
  set W : Matrix n n ℂ := (hMH.eigenvectorUnitary : Matrix n n ℂ) with hWdef
  have hW1 : W * Wᴴ = 1 := by
    rw [hWdef, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hW2 : Wᴴ * W = 1 := by
    rw [hWdef, ← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self]
  set μ := hMH.eigenvalues with hμ
  obtain ⟨b, hbdef⟩ : ∃ b : n → n → ℂ, ∀ k p, b k p = W p k := ⟨fun k p => W p k, fun _ _ => rfl⟩
  have hbev : ∀ k, M *ᵥ b k = μ k • b k := by
    intro k
    have hbk : b k = fun p => W p k := funext fun p => hbdef k p
    rw [hbk]
    have := eigvec_mulVec hMH k
    funext p
    have hp := congrFun this p
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul] at hp ⊢
    exact hp
  have hbn : ∀ k, ∑ p, Complex.normSq (b k p) = 1 := fun k => by
    simp only [hbdef]; exact col_normSq_of_unitary W hW2 k
  have hbdot : ∀ k, (star (b k) ⬝ᵥ b k).re = 1 := fun k => by rw [dot_star_self_re, hbn]
  have hstruct : ∀ k, P *ᵥ b k = b k ∨ P *ᵥ b k = 0 :=
    fun k => adapted_eigvec P Q hP hPP hQ (b k) (μ k) (hbev k)
  -- diagonal entries
  set d : n → ℝ := fun k => (star (b k) ⬝ᵥ (σ *ᵥ b k)).re with hd
  have hUB : vN σ ≤ ∑ k, ent (d k) := vN_le_diag_b hσH hσpsd W hW1 hW2 b hbdef
  set A := univ.filter (fun k => P *ᵥ b k = b k) with hAdef
  have hqPA : ∀ k, (star (b k) ⬝ᵥ (P *ᵥ b k)).re = if k ∈ A then 1 else 0 := by
    intro k
    by_cases hk : k ∈ A
    · rw [if_pos hk, (mem_filter.mp hk).2, hbdot]
    · rw [if_neg hk]
      rcases hstruct k with h | h
      · exact absurd (mem_filter.mpr ⟨mem_univ k, h⟩) hk
      · rw [h, dotProduct_zero, Complex.zero_re]
  have hcardA : (A.card : ℝ) = D := by
    have h := sum_quad_eq_trace_b W P hW1 b hbdef
    have h2 := congrArg Complex.re h
    rw [Complex.re_sum, htr, Complex.natCast_re] at h2
    simp only [hqPA] at h2
    rw [← h2, sum_boole]
    congr 2
    ext x
    simp
  -- values of `d`
  have hdA : ∀ k ∈ A, d k ≤ (D : ℝ)⁻¹ := by
    intro k hk
    simp only [hd]
    rw [hqσ]
    have e1 := (hq0 (b k)).2
    have e2 := (hq1 (b k)).2
    have e3 := (hq2 (b k)).2
    rw [hbn] at e1 e2 e3
    have : c * 3 = (D : ℝ)⁻¹ := by rw [hc]; field_simp
    nlinarith
  have hqM : ∀ k, (star (b k) ⬝ᵥ (M *ᵥ b k)).re = μ k := by
    intro k
    rw [hbev, dotProduct_smul, Complex.real_smul, Complex.re_ofReal_mul, hbdot, mul_one]
  have hKb : ∀ k, k ∉ A → (star (b k) ⬝ᵥ (M *ᵥ b k)).re =
      (star (b k) ⬝ᵥ (P₁ *ᵥ b k)).re + (star (b k) ⬝ᵥ (P₂ *ᵥ b k)).re := by
    intro k hk
    have hP0 : P *ᵥ b k = 0 := by
      rcases hstruct k with h | h
      · exact absurd (mem_filter.mpr ⟨mem_univ k, h⟩) hk
      · exact h
    have h1b : (1 - P) *ᵥ b k = b k := by rw [sub_mulVec, one_mulVec, hP0, sub_zero]
    have e1 : M *ᵥ b k = (1 - P) *ᵥ (Q *ᵥ b k) := by
      rw [hMdef, add_mulVec, smul_mulVec, hP0, smul_zero, zero_add, ← mulVec_mulVec,
        ← mulVec_mulVec, h1b]
    have e2 : star (b k) ⬝ᵥ ((1 - P) *ᵥ (Q *ᵥ b k)) = star (b k) ⬝ᵥ (Q *ᵥ b k) := by
      rw [dotProduct_mulVec, show star (b k) ᵥ* (1 - P) = star ((1 - P) *ᵥ b k) by
        rw [star_mulVec, h1H], h1b]
    rw [e1, e2, hQdef, add_mulVec, dotProduct_add, Complex.add_re]
  have hdK : ∀ k, k ∉ A → d k = c * μ k := by
    intro k hk
    simp only [hd]
    rw [hqσ, ← hqM k, hKb k hk]
    have : (star (b k) ⬝ᵥ (P *ᵥ b k)).re = 0 := by rw [hqPA, if_neg hk]
    rw [this, zero_add]
  have hμA : ∀ k ∈ A, μ k = 3 := by
    intro k hk
    have hPb := (mem_filter.mp hk).2
    have h1b : (1 - P) *ᵥ b k = 0 := by rw [sub_mulVec, one_mulVec, hPb, sub_self]
    rw [← hqM k, hMdef, add_mulVec, smul_mulVec, hPb, ← mulVec_mulVec, h1b, mulVec_zero,
      add_zero, dotProduct_smul, smul_eq_mul,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul, hbdot, mul_one]
  -- sums of `d`
  have hsumd : ∑ k, d k = 1 := by
    have h := congrArg Complex.re (sum_quad_eq_trace_b W σ hW1 b hbdef)
    rw [Complex.re_sum, hσtr] at h
    exact h
  have hsumA : ∑ k ∈ A, d k = (P * σ).trace.re := by
    have h := congrArg Complex.re (sum_quad_eq_trace_b W (P * σ * P) hW1 b hbdef)
    rw [Complex.re_sum, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP] at h
    rw [← h, ← sum_filter_add_sum_filter_not univ (fun k => P *ᵥ b k = b k)]
    have h0 : ∑ k ∈ univ.filter (fun k => ¬ P *ᵥ b k = b k),
        (star (b k) ⬝ᵥ ((P * σ * P) *ᵥ b k)).re = 0 := by
      refine sum_eq_zero fun k hk => ?_
      have hk' : k ∉ A := fun h => (mem_filter.mp hk).2 (mem_filter.mp h).2
      have hP0 : P *ᵥ b k = 0 := by
        rcases hstruct k with h | h
        · exact absurd (mem_filter.mpr ⟨mem_univ k, h⟩) hk'
        · exact h
      rw [← mulVec_mulVec, hP0, mulVec_zero, dotProduct_zero, Complex.zero_re]
    rw [h0, add_zero]
    refine sum_congr rfl fun k hk => ?_
    have hPb := (mem_filter.mp hk).2
    simp only [hd]
    rw [← mulVec_mulVec, hPb, ← mulVec_mulVec, dotProduct_mulVec (star (b k)) P,
      show star (b k) ᵥ* P = star (P *ᵥ b k) by rw [star_mulVec, hP], hPb]
  set w0 := 1 - (P * σ).trace.re with hw0def
  have hsumAc : ∑ k ∈ Aᶜ, d k = w0 := by
    have := sum_add_sum_compl A d
    rw [hsumd, hsumA] at this
    rw [hw0def]; linarith
  -- counting
  have hrankM : M.rank ≤ 3 * D := by
    have hrP : P.rank = D := rank_proj hP hPP D htr
    have h3P : ((3 : ℂ) • P).rank ≤ D := by
      rw [show (3 : ℂ) • P = ((3 : ℂ) • (1 : Matrix n n ℂ)) * P by
        rw [Matrix.smul_mul, Matrix.one_mul]]
      exact (rank_mul_le_right _ _).trans hrP.le
    have hK : ((1 - P) * Q * (1 - P)).rank ≤ 2 * D := by
      refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans ?_)
      refine (rank_add_le' P₁ P₂).trans ?_
      have r1 : P₁.rank ≤ D := by rw [hP₁]; exact (rank_conj_le _ _).trans hrP.le
      have r2 : P₂.rank ≤ D := by rw [hP₂]; exact (rank_conj_le _ _).trans hrP.le
      omega
    have := rank_add_le' ((3 : ℂ) • P) ((1 - P) * Q * (1 - P))
    rw [← hMdef] at this
    omega
  set S := Aᶜ.filter (fun k => μ k ≠ 0) with hSdef
  have hcardS : S.card ≤ 2 * D := by
    have hnz : (A ∪ S).card ≤ 3 * D := by
      have h1 : (A ∪ S).card ≤ (univ.filter fun k => μ k ≠ 0).card := by
        apply card_le_card
        intro k hk
        rcases mem_union.mp hk with h | h
        · simp [hμA k h]
        · simp only [hSdef, mem_filter] at h; simp [h.2]
      have h2 : (univ.filter fun k => μ k ≠ 0).card = M.rank := by
        rw [hMH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      omega
    have hdisj : Disjoint A S := by
      rw [disjoint_left]
      intro k hkA hkS
      simp only [hSdef, mem_filter, mem_compl] at hkS
      exact hkS.1 hkA
    rw [card_union_of_disjoint hdisj] at hnz
    have : (A.card : ℝ) = D := hcardA
    have hA' : A.card = D := by exact_mod_cast this
    omega
  -- entropy bounds
  have hd0 : ∀ k, 0 ≤ d k := fun k => hσpsd (b k)
  have hgroupA := ent_group_le A d D hD (by
    have : (A.card : ℝ) = D := hcardA; exact le_of_eq (by exact_mod_cast this))
    (fun k _ => hd0 k)
  have hgroupS := ent_group_le S d (2 * D) (by omega) hcardS (fun k _ => hd0 k)
  have hSsum : ∑ k ∈ S, d k = w0 := by
    rw [← hsumAc, hSdef, sum_filter]
    refine sum_congr rfl fun k hk => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [hdK k (mem_compl.mp hk), h, mul_zero]
  have hSent : ∑ k ∈ Aᶜ, ent (d k) = ∑ k ∈ S, ent (d k) := by
    rw [hSdef, sum_filter]
    refine sum_congr rfl fun k hk => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [hdK k (mem_compl.mp hk), h, mul_zero, ent_zero]
  have hsplit : ∑ k, ent (d k) = ∑ k ∈ A, ent (d k) + ∑ k ∈ Aᶜ, ent (d k) :=
    (sum_add_sum_compl A _).symm
  rw [hSsum] at hgroupS
  have hAsum : ∑ k ∈ A, d k = 1 - w0 := by rw [hsumA, hw0def]; ring
  rw [hAsum] at hgroupA
  have hw0nn : 0 ≤ w0 := by rw [← hsumAc]; exact sum_nonneg fun k _ => hd0 k
  have hlog2D : Real.log ((2 * D : ℕ) : ℝ) = Real.log 2 + Real.log D := by
    push_cast; rw [Real.log_mul (by norm_num) hDR.ne']
  rw [hlog2D] at hgroupS
  -- monotonicity in `w`
  have hl2 := log_two_gt_half
  have hmono1 : ent w0 ≤ ent w := by
    rcases (hw0nn.trans hw0).eq_or_lt with h | hwpos
    · have : w0 = 0 := by linarith
      rw [this, ent_zero, ← h, ent_zero]
    · have ht := ent_tangent hw0nn hwpos
      have hlw : Real.log w ≤ Real.log (1 / 4) := Real.log_le_log hwpos hw
      have h14 : Real.log (1 / 4) = -(2 * Real.log 2) := by
        rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; push_cast; ring
      have : 0 ≤ -Real.log w - 1 := by linarith
      nlinarith
  have hmono2 : ent (1 - w0) ≤ ent (1 - w) := by
    have h1w : 0 < 1 - w := by linarith
    have ht := ent_tangent (show 0 ≤ 1 - w0 by linarith) h1w
    have hl : -1 ≤ Real.log (1 - w) := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1w)
      rw [Real.log_inv] at this
      have h' : (1 - w)⁻¹ - 1 ≤ 1 := by
        rw [sub_le_iff_le_add, inv_le_iff_one_le_mul₀ h1w]; nlinarith
      linarith
    have : -Real.log (1 - w) - 1 ≤ 0 := by linarith
    nlinarith
  have hl2pos : 0 < Real.log 2 := by linarith
  calc vN σ ≤ ∑ k, ent (d k) := hUB
    _ = ∑ k ∈ A, ent (d k) + ∑ k ∈ S, ent (d k) := by rw [hsplit, hSent]
    _ ≤ (ent (1 - w0) + (1 - w0) * Real.log D) + (ent w0 + w0 * (Real.log 2 + Real.log D)) :=
        add_le_add hgroupA hgroupS
    _ = Real.log D + ent w0 + ent (1 - w0) + w0 * Real.log 2 := by ring
    _ ≤ Real.log D + ent w + ent (1 - w) + w * Real.log 2 := by nlinarith

/-- **Proposition `prop:dimension-perm`** from strong subadditivity for commuting pinchings alone. -/
theorem dimension_perm_of_SSA (hQ : QIT_CommutingPinchingSSA.{u}) {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_QIT_gen hQ genTwirlBound φ δ hrel hγ N A hN hA hδ

end Houghton
