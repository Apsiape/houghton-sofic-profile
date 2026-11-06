import FiniteLean.QIT.Entropy.Spectral
import Houghton.Analysis.SectorQIT

/-!
# Elementary spectral facts: proof of `SubStateEntropy`

Spectral decomposition `A = U diag(λ) U*` of Hermitian matrices (Mathlib), the quadratic-form
identity `⟨v, A v⟩ = ∑ λⱼ |(U* v)ⱼ|²`, and the bound `S(ρ̂) ≥ log D` from `λⱼ ≤ 1/D`.
-/

universe u

namespace Houghton

open Finset Equiv Matrix ComplexConjugate

section State

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

lemma YhY (c : Fin N → Perm Ω) :
    (Ymat c)ᴴ * Ymat c = ((9 : ℂ) ^ N) • (1 : Matrix Ω Ω ℂ) := by
  ext ω ω'
  simp only [mul_apply, conjTranspose_apply, Ymat, Matrix.smul_apply, one_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, sum_comm]
  have h : ∀ α, ∑ χ, star (Msec c χ α ω) * Msec c χ α ω' =
      3 ^ N * ∑ g, conj (pm (fprod c g) α ω) * pm (fprod c g) α ω' := by
    intro α
    exact parseval_scalar (fun g => pm (fprod c g) α ω) (fun g => pm (fprod c g) α ω')
  simp only [h, ← mul_sum]
  rw [sum_comm]
  have h2 : ∀ g, ∑ α, conj (pm (fprod c g) α ω) * pm (fprod c g) α ω' =
      if ω = ω' then 1 else 0 := by
    intro g
    simp only [pm, apply_ite conj, map_one, map_zero, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq']
    simp only [mem_univ, if_true]
    by_cases h : ω = ω'
    · subst h; simp
    · simp [h, (fprod c g).injective.ne h]
  simp only [h2, sum_const, card_univ, card_G, nsmul_eq_mul]
  rw [show (9 : ℂ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
  push_cast
  ring

lemma rhoSec_cap (c : Fin N → Perm Ω) (hD : 0 < Fintype.card Ω) (v : (Fin N → Fin 3) × Ω → ℂ) :
    (star v ⬝ᵥ (rhoSec c *ᵥ v)).re ≤
      (Fintype.card Ω : ℝ)⁻¹ * ∑ j, Complex.normSq (v j) := by
  have hK : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  set W := (Ymat c)ᴴ *ᵥ v with hW
  have e : star v ⬝ᵥ (rhoSec c *ᵥ v) =
      (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (star W ⬝ᵥ W) := by
    rw [rhoSec, smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec,
      star_mulVec, conjTranspose_conjTranspose]
  rw [e, Complex.real_smul, Complex.re_ofReal_mul, dot_star_self_re]
  -- `‖W‖² ≤ 9^N ‖v‖²`
  set a := ∑ j, Complex.normSq (W j)
  set b := ∑ j, Complex.normSq (v j)
  have ha : 0 ≤ a := sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hb : 0 ≤ b := sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have h9 : Real.sqrt (9 ^ N) = 3 ^ N := by
    rw [show (9 : ℝ) ^ N = (3 ^ N) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      Real.sqrt_sq (by positivity)]
  have hYW : ∑ j, Complex.normSq ((Ymat c *ᵥ W) j) = 9 ^ N * a := by
    rw [← dot_star_self_re, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, YhY, smul_mulVec,
      one_mulVec, dotProduct_smul, smul_eq_mul,
      show ((9 : ℂ) ^ N) = (((9 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      dot_star_self_re]
  have hA : a = (star v ⬝ᵥ (Ymat c *ᵥ W)).re := by
    rw [dotProduct_mulVec,
      show star v ᵥ* Ymat c = star W by rw [hW, star_mulVec, conjTranspose_conjTranspose],
      dot_star_self_re]
  have hcs := re_dot_le v (Ymat c *ᵥ W)
  rw [← hA, hYW, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 9 ^ N), h9] at hcs
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have h3 : (0 : ℝ) < 3 ^ N := by positivity
  have key : a ≤ 9 ^ N * b := by
    have hroot : Real.sqrt a ≤ 3 ^ N * Real.sqrt b := by
      rcases hsa0.eq_or_lt with h0 | hpos
      · rw [← h0]; positivity
      · nlinarith
    have h9' : (9 : ℝ) ^ N = 3 ^ N * 3 ^ N := by rw [← mul_pow]; norm_num
    rw [← hsa, h9', ← hsb]
    nlinarith
  have hD' : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  rw [inv_mul_le_iff₀ hK]
  calc a ≤ 9 ^ N * b := key
    _ = 9 ^ N * (Fintype.card Ω : ℝ) * ((Fintype.card Ω : ℝ)⁻¹ * b) := by
        field_simp

theorem subStateEntropy : SubStateEntropy.{u} := by
  intro Ω _ _ N c hD
  exact log_le_vN_of_cap (rhoSec_density c hD) _ (by exact_mod_cast hD) (rhoSec_cap c hD)

end State

/-! ### `SubSectorEntropy`: the dephased state has entropy `≥ H(pSec)` -/

section Sector

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

lemma pinch_labelProj (i : Fin N) (X : Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ)
    (p q : (Fin N → Fin 3) × Ω) :
    pinch (labelProj i) X p q = if p.1 i = q.1 i then X p q else 0 := by
  simp only [pinch, labelProj, Matrix.sum_apply, diagonal_mul, mul_diagonal]
  by_cases h : p.1 i = q.1 i
  · rw [if_pos h, sum_eq_single (p.1 i)]
    · simp [h]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp
  · rw [if_neg h]
    refine sum_eq_zero fun a _ => ?_
    by_cases ha : p.1 i = a
    · have : ¬ q.1 i = a := fun hq => h (ha.trans hq.symm)
      simp [ha, this]
    · simp [ha]

lemma pinchAll_labelProj : ∀ (m : ℕ) (e : Fin m → Fin N)
    (X : Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ) (p q : (Fin N → Fin 3) × Ω),
    pinchAll (fun k => labelProj (Ω := Ω) (e k)) X p q =
      if (∀ k, p.1 (e k) = q.1 (e k)) then X p q else 0
  | 0, e, X, p, q => by simp [pinchAll]
  | m + 1, e, X, p, q => by
    simp only [pinchAll]
    rw [pinch_labelProj]
    have ih := pinchAll_labelProj m (fun k => e k.succ) X p q
    rw [ih]
    by_cases h0 : p.1 (e 0) = q.1 (e 0)
    · simp only [h0, if_true, Fin.forall_fin_succ, true_and]
    · simp [h0, Fin.forall_fin_succ]

lemma rhoSec_apply (c : Fin N → Perm Ω) (p q : (Fin N → Fin 3) × Ω) :
    rhoSec c p q = (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) *
      ∑ ω, Msec c p.1 p.2 ω * conj (Msec c q.1 q.2 ω) := by
  simp only [rhoSec, Matrix.smul_apply, mul_apply, conjTranspose_apply, Ymat, Complex.real_smul]
  rfl

theorem subSectorEntropy : SubSectorEntropy.{u} := by
  intro Ω _ _ N c hD
  have hK : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  obtain ⟨hρH, hρpsd, -⟩ := rhoSec_density c hD
  set ρ := rhoSec c with hρdef
  set σ := pinchAll (fun i => labelProj (Ω := Ω) i) ρ with hσdef
  have hσ : ∀ p q, σ p q = if p.1 = q.1 then ρ p q else 0 := by
    intro p q
    have := pinchAll_labelProj N (fun i => i) ρ p q
    rw [hσdef, this]
    by_cases h : p.1 = q.1
    · rw [if_pos (fun k => congrFun h k), if_pos h]
    · rw [if_neg h, if_neg (fun hk => h (funext hk))]
  have hH : σ.IsHermitian := by
    ext p q
    rw [conjTranspose_apply, hσ, hσ]
    by_cases h : p.1 = q.1
    · rw [if_pos h.symm, if_pos h]
      have := congrFun (congrFun hρH p) q
      rw [conjTranspose_apply] at this
      exact this
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [vN_eq hH]
  set U := (hH.eigenvectorUnitary :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ) with hU
  set lam := hH.eigenvalues with hlam
  -- block masses of the eigenvectors
  set π : (Fin N → Fin 3) × Ω → (Fin N → Fin 3) → ℝ :=
    fun j χ => ∑ α, Complex.normSq (U (χ, α) j) with hπdef
  have hπ0 : ∀ j χ, 0 ≤ π j χ := fun j χ => sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hπsum : ∀ j, ∑ χ, π j χ = 1 := by
    intro j
    rw [← eigvec_normSq_sum hH j, Fintype.sum_prod_type]
  -- diagonal of `ρ`
  have hρdiag : ∀ χ, ∑ α, (ρ (χ, α) (χ, α)).re = pSec c χ := by
    intro χ
    simp only [hρdef, rhoSec_apply, Complex.re_ofReal_mul, ← mul_sum, pSec, nsq]
    rw [div_eq_inv_mul]
    congr 1
    refine sum_congr rfl fun α _ => ?_
    rw [Complex.re_sum]
    refine sum_congr rfl fun ω _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  have hp : ∀ χ, pSec c χ = ∑ j, lam j * π j χ := by
    intro χ
    rw [← hρdiag]
    simp only [hπdef, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun α _ => ?_
    have := herm_diag_re hH (χ, α)
    rw [hσ, if_pos rfl] at this
    exact this
  -- the eigen-relation on blocks
  have hblock : ∀ j χ, lam j * π j χ ≤ pSec c χ * π j χ ∧ 0 ≤ lam j * π j χ := by
    intro j χ
    set u : (Fin N → Fin 3) × Ω → ℂ := fun p => if p.1 = χ then U p j else 0 with hu
    have hev := eigvec_mulVec hH j
    -- `ρ u = λ u` on the block
    have hρu : ∀ p, p.1 = χ → (ρ *ᵥ u) p = (lam j : ℂ) * U p j := by
      intro p hp1
      have := congrFun hev p
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [← this]
      refine sum_congr rfl fun q _ => ?_
      rw [hσ]
      simp only [hu]
      by_cases hq : q.1 = χ
      · simp [hq, show p.1 = q.1 from hp1.trans hq.symm, hU]
      · simp [hq, show ¬ p.1 = q.1 from fun h => hq (h.symm.trans hp1)]
    have hnorm : ∑ p, Complex.normSq (u p) = π j χ := by
      rw [Fintype.sum_prod_type, hπdef]
      simp only [hu]
      rw [sum_eq_single χ]
      · simp
      · intro χ' _ hχ'; simp [hχ']
      · simp
    have hquad : (star u ⬝ᵥ (ρ *ᵥ u)).re = lam j * π j χ := by
      rw [← hnorm, mul_sum]
      simp only [dotProduct, Complex.re_sum, Pi.star_apply]
      refine sum_congr rfl fun p _ => ?_
      by_cases hp1 : p.1 = χ
      · rw [hρu p hp1]
        simp only [hu, if_pos hp1]
        rw [mul_left_comm, Complex.re_ofReal_mul,
          show star (U p j) = conj (U p j) from rfl, ← Complex.normSq_eq_conj_mul_self,
          Complex.ofReal_re]
      · simp [hu, hp1]
    -- Gram bound
    have hgram : (star u ⬝ᵥ (ρ *ᵥ u)).re ≤ pSec c χ * π j χ := by
      have e : star u ⬝ᵥ (ρ *ᵥ u) =
          (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (star ((Ymat c)ᴴ *ᵥ u) ⬝ᵥ ((Ymat c)ᴴ *ᵥ u)) := by
        rw [hρdef, rhoSec, smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec,
          star_mulVec, conjTranspose_conjTranspose]
      rw [e, Complex.real_smul, Complex.re_ofReal_mul, dot_star_self_re, ← hnorm]
      have hω : ∀ ω, Complex.normSq (((Ymat c)ᴴ *ᵥ u) ω) ≤
          (∑ α, Complex.normSq (Msec c χ α ω)) * ∑ p, Complex.normSq (u p) := by
        intro ω
        set a : (Fin N → Fin 3) × Ω → ℂ := fun p => if p.1 = χ then Ymat c p ω else 0
        have e1 : ((Ymat c)ᴴ *ᵥ u) ω = star a ⬝ᵥ u := by
          simp only [mulVec, dotProduct, conjTranspose_apply, Pi.star_apply, a]
          refine sum_congr rfl fun p _ => ?_
          by_cases hp1 : p.1 = χ
          · simp [hp1]
          · simp [hp1, hu]
        have e2 : ∑ p, Complex.normSq (a p) = ∑ α, Complex.normSq (Msec c χ α ω) := by
          rw [Fintype.sum_prod_type, sum_eq_single χ]
          · simp [a, Ymat]
          · intro χ' _ hχ'; simp [a, hχ']
          · simp
        rw [e1, ← e2]
        exact normSq_dot_le a u
      have hsum : ∑ ω, Complex.normSq (((Ymat c)ᴴ *ᵥ u) ω) ≤
          nsq (Msec c χ) * ∑ p, Complex.normSq (u p) := by
        calc ∑ ω, Complex.normSq (((Ymat c)ᴴ *ᵥ u) ω)
            ≤ ∑ ω, (∑ α, Complex.normSq (Msec c χ α ω)) * ∑ p, Complex.normSq (u p) :=
              sum_le_sum fun ω _ => hω ω
          _ = nsq (Msec c χ) * ∑ p, Complex.normSq (u p) := by
              rw [← sum_mul, nsq, sum_comm]
      have hinv : (0 : ℝ) ≤ ((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ := inv_nonneg.mpr hK.le
      calc ((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ * ∑ ω, Complex.normSq (((Ymat c)ᴴ *ᵥ u) ω)
          ≤ ((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ * (nsq (Msec c χ) * ∑ p, Complex.normSq (u p)) :=
            mul_le_mul_of_nonneg_left hsum hinv
        _ = pSec c χ * ∑ p, Complex.normSq (u p) := by
            rw [pSec, div_eq_inv_mul, mul_assoc]
    have hpsd := hρpsd u
    rw [hquad] at hgram hpsd
    exact ⟨hgram, hpsd⟩
  -- Gibbs inequality
  have hterm : ∀ j χ, lam j * π j χ * (-Real.log (pSec c χ)) ≤
      lam j * π j χ * (-Real.log (lam j)) := by
    intro j χ
    obtain ⟨h1, h2⟩ := hblock j χ
    rcases h2.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hπpos : 0 < π j χ := by
        rcases (hπ0 j χ).eq_or_lt with h | h
        · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
        · exact h
      have hlpos : 0 < lam j := by
        by_contra hneg
        push Not at hneg
        nlinarith
      have hle : lam j ≤ pSec c χ := le_of_mul_le_mul_right h1 hπpos
      have := Real.log_le_log hlpos hle
      nlinarith
  calc ∑ χ, ent (pSec c χ) = ∑ χ, ∑ j, lam j * π j χ * (-Real.log (pSec c χ)) := by
        refine sum_congr rfl fun χ _ => ?_
        rw [← sum_mul, ← hp]; unfold ent; ring
    _ ≤ ∑ χ, ∑ j, lam j * π j χ * (-Real.log (lam j)) :=
        sum_le_sum fun χ _ => sum_le_sum fun j _ => hterm j χ
    _ = ∑ j, ent (lam j) := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        have : ∑ χ, lam j * π j χ * (-Real.log (lam j)) =
            lam j * (-Real.log (lam j)) * ∑ χ, π j χ := by
          rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring
        rw [this, hπsum, mul_one]; unfold ent; ring

end Sector

/-- **Proposition `prop:dimension-perm`** from strong subadditivity for commuting pinchings and the
single-dephasing bound (B); (A) and (C) are proved. -/
theorem dimension_perm_of_QIT_twirl (hQ : QIT_CommutingPinchingSSA.{u})
    (hB : SubTwirlEntropy.{u}) {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA' : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_QIT hQ subStateEntropy hB subSectorEntropy φ δ hrel hγ N A hN hA' hδ

end Houghton
