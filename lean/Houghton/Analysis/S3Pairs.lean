import Houghton.Analysis.Hamming
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The `S₃` pairs of Proposition `prop:dimension-perm`

From an assignment `φ : F →* Perm Ω` with relator defects `≤ δ`, the pairs
`A_i = φ(σ_{3i})`, `B_i = φ(σ_{3i+1})` (`0 ≤ i < N`) are rounded (Lemma `lem:s3round`, in its
permutation form) to exact local `S₃`-actions `x_i = u_i(s)`, `c_i = u_i(st)`, and the far-commutator
bound `A*(3N) ≤ A` together with transport in measure bounds all cross commutators.
-/

namespace Houghton

open Finset Equiv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

section Words

variable (φ : F →* Perm Ω)

omit [Fintype Ω] [DecidableEq Ω] in
lemma phi_sigma (j : ℕ) : φ (σ j) = φ a ^ j * φ α * (φ a ^ j)⁻¹ := by
  simp [σ, map_mul, map_pow, map_inv, inv_pow]

omit [Fintype Ω] [DecidableEq Ω] in
lemma conj_mul_conj (k g h : Perm Ω) : k * g * k⁻¹ * (k * h * k⁻¹) = k * (g * h) * k⁻¹ := by
  simp only [mul_assoc, inv_mul_cancel_left]

omit [Fintype Ω] [DecidableEq Ω] in
lemma conj_cube (k g : Perm Ω) : (k * g * k⁻¹) ^ 3 = k * g ^ 3 * k⁻¹ := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_mul_cancel_left]

omit [Fintype Ω] [DecidableEq Ω] in
lemma phi_sigma_sq (j : ℕ) : φ (σ j) * φ (σ j) = φ a ^ j * (φ α * φ α) * (φ a ^ j)⁻¹ := by
  rw [phi_sigma, conj_mul_conj]

omit [Fintype Ω] [DecidableEq Ω] in
lemma phi_sigma_mul_succ (j : ℕ) :
    φ (σ j) * φ (σ (j + 1)) = φ a ^ j * φ γ * (φ a ^ j)⁻¹ := by
  rw [phi_sigma, phi_sigma]
  simp only [γ, map_mul, map_inv, pow_succ, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

omit [Fintype Ω] [DecidableEq Ω] in
lemma phi_r₁ : φ r₁ = φ α * φ α := by
  simp [r₁, pow_two]

omit [Fintype Ω] [DecidableEq Ω] in
lemma phi_r₂ : φ r₂ = (φ γ) ^ 3 := by
  simp only [r₂, γ, map_pow, map_mul, map_inv, mul_assoc]

variable (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
include hrel

lemma dH_sigma_sq (j : ℕ) : dH (φ (σ j) * φ (σ j)) 1 ≤ δ := by
  rw [phi_sigma_sq, dH_conj, ← phi_r₁]
  exact hrel 0

lemma dH_sigma_braid (j : ℕ) : dH ((φ (σ j) * φ (σ (j + 1))) ^ 3) 1 ≤ δ := by
  rw [phi_sigma_mul_succ, conj_cube, dH_conj, ← phi_r₂]
  exact hrel 1

lemma dH_sigma_far (A : ℕ) (M : ℕ) (hA : AstarLE M A) (hδ : 0 ≤ δ) (p q : ℕ) (hp : p ≤ M)
    (hq : q ≤ M) (hpq : p + 2 ≤ q ∨ q + 2 ≤ p) :
    dH (φ (σ p) * φ (σ q)) (φ (σ q) * φ (σ p)) ≤ A * δ := by
  have h := hA p q hp hq hpq true true
  rw [ite_eq_left rfl, ite_eq_left rfl] at h
  have h2 := dH_le_of_areaLE φ δ hrel hδ h
  rw [dH_comm_eq]
  simpa [comm, map_mul, map_inv] using h2

end Words

lemma dH_sigma_gamma (φ : F →* Perm Ω) (j : ℕ) :
    dH (φ (σ j) * φ (σ (j + 1))) 1 = dH (φ γ) 1 := by
  rw [phi_sigma_mul_succ, dH_conj]

/-! ### The rounded local `S₃` actions -/

section Pairs

variable (φ : F →* Perm Ω) (N : ℕ)

/-- `A_i = φ(σ_{3i})`. -/
def pA (i : Fin N) : Perm Ω := φ (σ (3 * i.val))
/-- `B_i = φ(σ_{3i+1})`. -/
def pB (i : Fin N) : Perm Ω := φ (σ (3 * i.val + 1))
/-- `x_i = u_i(s)`: the rounded involution. -/
def px (i : Fin N) : Perm Ω := roundInv (pA φ N i)
/-- The rounded involution near `B_i`. -/
def pT (i : Fin N) : Perm Ω := roundInv (pB φ N i)
/-- `c_i = u_i(st)`: the rounded three-cycle. -/
def pc (i : Fin N) : Perm Ω := round3 (px φ N i * pT φ N i)

omit [Fintype Ω] in
lemma pc_pow_three (i : Fin N) : pc φ N i ^ 3 = 1 := round3_pow_three _

omit [Fintype Ω] in
lemma px_sq (i : Fin N) : px φ N i ^ 2 = 1 := roundInv_sq _

omit [Fintype Ω] in
lemma px_pc_px (i : Fin N) : px φ N i * pc φ N i * px φ N i = (pc φ N i)⁻¹ :=
  round3_conj _ _ (roundInv_mul_self _) (roundInv_mul_self _)

variable (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
include hrel

lemma dH_px (i : Fin N) : dH (px φ N i) (pA φ N i) ≤ δ :=
  (dH_roundInv _).trans (dH_sigma_sq φ δ hrel _)

lemma dH_pT (i : Fin N) : dH (pT φ N i) (pB φ N i) ≤ δ :=
  (dH_roundInv _).trans (dH_sigma_sq φ δ hrel _)

lemma dH_pc_ST (i : Fin N) : dH (pc φ N i) (px φ N i * pT φ N i) ≤ 7 * δ := by
  have h1 := dH_px φ N δ hrel i
  have h2 := dH_pT φ N δ hrel i
  have hST : dH (px φ N i * pT φ N i) (pA φ N i * pB φ N i) ≤ 2 * δ := by
    have := dH_mul_le (px φ N i) (pT φ N i) (pA φ N i) (pB φ N i)
    linarith
  have hbraid : dH ((pA φ N i * pB φ N i) ^ 3) 1 ≤ δ := dH_sigma_braid φ δ hrel _
  have hcube : dH ((px φ N i * pT φ N i) ^ 3) ((pA φ N i * pB φ N i) ^ 3) ≤ 3 * (2 * δ) := by
    have := dH_pow_le (px φ N i * pT φ N i) (pA φ N i * pB φ N i) 3
    push_cast at this
    linarith
  have hr := dH_round3 (px φ N i * pT φ N i)
  have t1 := dH_triangle ((px φ N i * pT φ N i) ^ 3) ((pA φ N i * pB φ N i) ^ 3) 1
  unfold pc
  linarith

lemma dH_pc (i : Fin N) : dH (pc φ N i) (pA φ N i * pB φ N i) ≤ 9 * δ := by
  have h1 := dH_px φ N δ hrel i
  have h2 := dH_pT φ N δ hrel i
  have hST : dH (px φ N i * pT φ N i) (pA φ N i * pB φ N i) ≤ 2 * δ := by
    have := dH_mul_le (px φ N i) (pT φ N i) (pA φ N i) (pB φ N i)
    linarith
  have h7 := dH_pc_ST φ N δ hrel i
  have t2 := dH_triangle (pc φ N i) (px φ N i * pT φ N i) (pA φ N i * pB φ N i)
  linarith

/-- `u_i(t) = x_i c_i` is within `8δ` of `B_i`. -/
lemma dH_pt (i : Fin N) : dH (px φ N i * pc φ N i) (pB φ N i) ≤ 8 * δ := by
  have h7 := dH_pc_ST φ N δ hrel i
  have h2 := dH_pT φ N δ hrel i
  have hxx : px φ N i * (px φ N i * pT φ N i) = pT φ N i := by
    rw [← mul_assoc, px, roundInv_mul_self, one_mul]
  have t := dH_triangle (px φ N i * pc φ N i) (px φ N i * (px φ N i * pT φ N i)) (pB φ N i)
  rw [dH_mul_left, hxx] at t
  linarith

lemma dH_pc_one (hγ : 1 / 2 ≤ dH (φ γ) 1) (i : Fin N) : 1 / 2 - 9 * δ ≤ dH (pc φ N i) 1 := by
  have h := dH_pc φ N δ hrel i
  have hg : dH (pA φ N i * pB φ N i) 1 = dH (φ γ) 1 := dH_sigma_gamma φ _
  have t := dH_triangle (pA φ N i * pB φ N i) (pc φ N i) 1
  rw [dH_comm (pA φ N i * pB φ N i) (pc φ N i)] at t
  linarith

variable (A : ℕ) (hA : AstarLE (3 * N) A) (hδ : 0 ≤ δ)
include hA hδ

lemma far_pairs (i j : Fin N) (hij : i ≠ j) (e e' : Bool) :
    dH ((if e then pA φ N i else pB φ N i) * (if e' then pA φ N j else pB φ N j))
      ((if e' then pA φ N j else pB φ N j) * (if e then pA φ N i else pB φ N i)) ≤ A * δ := by
  have hi := i.isLt
  have hj := j.isLt
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  cases e <;> cases e' <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, pA, pB] <;>
    exact dH_sigma_far φ δ hrel A (3 * N) hA hδ _ _ (by omega) (by omega) (by omega)

lemma dH_pc_comm (i j : Fin N) (hij : i ≠ j) :
    dH (pc φ N i * pc φ N j) (pc φ N j * pc φ N i) ≤ 4 * (A * δ) + 36 * δ := by
  set Ai := pA φ N i
  set Bi := pB φ N i
  set Aj := pA φ N j
  set Bj := pB φ N j
  have f := far_pairs φ N δ hrel A hA hδ i j hij
  have fAA := f true true
  have fAB := f true false
  have fBA := f false true
  have fBB := f false false
  simp only [ite_true, Bool.false_eq_true, ite_false] at fAA fAB fBA fBB
  -- the four interchanges
  have m1 : dH (Ai * Bi * Aj) (Aj * (Ai * Bi)) ≤ 2 * (A * δ) := by
    have := dH_mul_commutes Ai Bi Aj; linarith
  have m2 : dH (Ai * Bi * Bj) (Bj * (Ai * Bi)) ≤ 2 * (A * δ) := by
    have := dH_mul_commutes Ai Bi Bj; linarith
  have mid : dH (Ai * Bi * (Aj * Bj)) (Aj * Bj * (Ai * Bi)) ≤ 4 * (A * δ) := by
    have := dH_commutes_mul (Ai * Bi) Aj Bj
    rw [dH_comm (Ai * Bi * Aj), dH_comm (Ai * Bi * Bj)] at this
    rw [dH_comm] at m1 m2
    linarith
  have ci := dH_pc φ N δ hrel i
  have cj := dH_pc φ N δ hrel j
  have e1 : dH (pc φ N i * pc φ N j) (Ai * Bi * (Aj * Bj)) ≤ 18 * δ := by
    have := dH_mul_le (pc φ N i) (pc φ N j) (Ai * Bi) (Aj * Bj); linarith
  have e2 : dH (Aj * Bj * (Ai * Bi)) (pc φ N j * pc φ N i) ≤ 18 * δ := by
    have := dH_mul_le (pc φ N j) (pc φ N i) (Aj * Bj) (Ai * Bi)
    rw [dH_comm]; linarith
  have t1 := dH_triangle (pc φ N i * pc φ N j) (Ai * Bi * (Aj * Bj)) (pc φ N j * pc φ N i)
  have t2 := dH_triangle (Ai * Bi * (Aj * Bj)) (Aj * Bj * (Ai * Bi)) (pc φ N j * pc φ N i)
  linarith

lemma dH_px_comm (i j : Fin N) (hij : i ≠ j) :
    dH (px φ N i * pc φ N j) (pc φ N j * px φ N i) ≤ 2 * (A * δ) + 20 * δ := by
  set Ai := pA φ N i
  set Aj := pA φ N j
  set Bj := pB φ N j
  have f := far_pairs φ N δ hrel A hA hδ i j hij
  have fAA := f true true
  have fAB := f true false
  simp only [ite_true, Bool.false_eq_true, ite_false] at fAA fAB
  have mid : dH (Ai * (Aj * Bj)) (Aj * Bj * Ai) ≤ 2 * (A * δ) := by
    have := dH_commutes_mul Ai Aj Bj; linarith
  have xi := dH_px φ N δ hrel i
  have cj := dH_pc φ N δ hrel j
  have e1 : dH (px φ N i * pc φ N j) (Ai * (Aj * Bj)) ≤ 10 * δ := by
    have := dH_mul_le (px φ N i) (pc φ N j) Ai (Aj * Bj); linarith
  have e2 : dH (Aj * Bj * Ai) (pc φ N j * px φ N i) ≤ 10 * δ := by
    have := dH_mul_le (pc φ N j) (px φ N i) (Aj * Bj) Ai
    rw [dH_comm]; linarith
  have t1 := dH_triangle (px φ N i * pc φ N j) (Ai * (Aj * Bj)) (pc φ N j * px φ N i)
  have t2 := dH_triangle (Ai * (Aj * Bj)) (Aj * Bj * Ai) (pc φ N j * px φ N i)
  linarith

end Pairs

/-- **Reduction.** Under the hypotheses of Proposition `prop:dimension-perm`, there are exact local
`S₃`-actions (`c_i³ = x_i² = 1`, `x_i c_i x_i = c_i⁻¹`) with displacement `≥ 1/8` and with
row sums of cross-commutator defects `≤ 1/40000`. -/
theorem exists_local_S3 (φ : F →* Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1 / 2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA : AstarLE (3 * N) A)
    (hδ : (10 : ℝ) ^ 8 * N * max 1 (A : ℝ) * δ ≤ 1) :
    ∃ c x : Fin N → Perm Ω,
      (∀ i, c i ^ 3 = 1) ∧ (∀ i, x i ^ 2 = 1) ∧ (∀ i, x i * c i * x i = (c i)⁻¹) ∧
      (∀ i, (1 : ℝ) / 8 ≤ dH (c i) 1) ∧
      (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) ≤ 1 / 40000) ∧
      (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i) ≤ 1 / 40000) := by
  have hδ0 : 0 ≤ δ := (dH_nonneg _ _).trans (hrel 0)
  set M : ℝ := max 1 (A : ℝ) with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMA : (A : ℝ) ≤ M := le_max_right _ _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNM : (1 : ℝ) ≤ N * M := by nlinarith
  have hNMδ : (N : ℝ) * M * δ ≤ 1 / 10 ^ 8 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hδsmall : δ ≤ 1 / 10 ^ 8 := by
    have : δ ≤ N * M * δ := by nlinarith
    linarith
  have hAδ : (A : ℝ) * δ ≤ M * δ := mul_le_mul_of_nonneg_right hMA hδ0
  have hδM : δ ≤ M * δ := by nlinarith
  refine ⟨pc φ N, px φ N, pc_pow_three φ N, px_sq φ N, px_pc_px φ N, ?_, ?_, ?_⟩
  · intro i
    have := dH_pc_one φ N δ hrel hγ i
    linarith
  · intro i
    have hb : ∀ j ∈ univ.filter (· ≠ i),
        dH (pc φ N i * pc φ N j) (pc φ N j * pc φ N i) ≤ 40 * (M * δ) := by
      intro j hj
      have hij : i ≠ j := fun h => (mem_filter.mp hj).2 h.symm
      have := dH_pc_comm φ N δ hrel A hA hδ0 i j hij
      linarith
    calc ∑ j ∈ univ.filter (· ≠ i), dH (pc φ N i * pc φ N j) (pc φ N j * pc φ N i)
        ≤ (univ.filter (· ≠ i)).card • (40 * (M * δ)) := sum_le_card_nsmul _ _ _ hb
      _ ≤ (N : ℝ) * (40 * (M * δ)) := by
          rw [nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by nlinarith)
          have : (univ.filter (· ≠ i)).card ≤ N :=
            (card_filter_le _ _).trans (by simp)
          exact_mod_cast this
      _ ≤ 1 / 40000 := by nlinarith
  · intro i
    have hb : ∀ j ∈ univ.filter (· ≠ i),
        dH (px φ N i * pc φ N j) (pc φ N j * px φ N i) ≤ 40 * (M * δ) := by
      intro j hj
      have hij : i ≠ j := fun h => (mem_filter.mp hj).2 h.symm
      have := dH_px_comm φ N δ hrel A hA hδ0 i j hij
      linarith
    calc ∑ j ∈ univ.filter (· ≠ i), dH (px φ N i * pc φ N j) (pc φ N j * px φ N i)
        ≤ (univ.filter (· ≠ i)).card • (40 * (M * δ)) := sum_le_card_nsmul _ _ _ hb
      _ ≤ (N : ℝ) * (40 * (M * δ)) := by
          rw [nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ (by nlinarith)
          have : (univ.filter (· ≠ i)).card ≤ N :=
            (card_filter_le _ _).trans (by simp)
          exact_mod_cast this
      _ ≤ 1 / 40000 := by nlinarith

end Houghton
