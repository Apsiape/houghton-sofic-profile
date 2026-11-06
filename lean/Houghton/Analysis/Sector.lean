import Houghton.Analysis.S3Pairs
import Houghton.Analysis.PermMatrix
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Proposition `prop:dimension-perm` from the entropic sector bound

`PermSectorLemma` is Lemma `lem:sector` of the paper for unitary representations by permutation
matrices: a representation `u : S₃ → U(D)` by permutation matrices is a pair of permutations `s, t`
with `s² = t² = (st)³ = 1`, its values are the six normal forms `1, s, t, st, ts, sts`, the
three-cycle is `c = st`, and `‖P_g - P_h‖₂² = 2 dH g h`.  So `‖u_i(c) - I‖₂ ≥ Δ` reads
`Δ² ≤ 2 dH (s_i t_i) 1`, and `t = √(2N) η` with `η` the maximal `‖·‖₂`-commutator reads
`4 N dH(...) ≤ t²` for every pair of normal forms.  Logarithms are base `2`.
-/

universe u

namespace Houghton

open Finset Equiv

/-- Binary entropy in bits. -/
noncomputable def h2 (p : ℝ) : ℝ := -(p * Real.logb 2 p) - (1 - p) * Real.logb 2 (1 - p)

/-- The six normal forms `1, s, t, st, ts, sts` of `S₃ = ⟨s, t | s², t², (st)³⟩`. -/
def nf {X : Type*} (s t : Perm X) : Fin 6 → Perm X := ![1, s, t, s * t, t * s, s * t * s]

/-- **Lemma `lem:sector`** (entropic sector bound), permutation-matrix case. -/
def PermSectorLemma : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (s t : Fin N → Perm Ω) (Δ τ : ℝ),
    (∀ i, s i ^ 2 = 1) → (∀ i, t i ^ 2 = 1) → (∀ i, (s i * t i) ^ 3 = 1) →
    0 ≤ Δ → (∀ i, Δ ^ 2 ≤ 2 * dH (s i * t i) 1) →
    0 ≤ τ →
    (∀ i j, i ≠ j → ∀ k l,
      4 * N * dH (nf (s i) (t i) k * nf (s j) (t j) l) (nf (s j) (t j) l * nf (s i) (t i) k)
        ≤ τ ^ 2) →
    τ ≤ Δ → τ ^ 2 ≤ 5 / 6 →
    N * ((Δ - τ) ^ 2 / 3 - h2 (τ ^ 2) - τ ^ 2 * Real.logb 2 5) ≤ Real.logb 2 (Fintype.card Ω)

/-- **Lemma `lem:sector`** in the paper's matrix language, for representations `u_i : S₃ → U(D)` by
permutation matrices `P_g` (`hs2 T = ‖T‖₂² = D⁻¹ Tr(TᵀT)`): `‖u_i(c) - I‖₂ ≥ Δ` and
`‖[u_i(g), u_j(h)]‖₂ ≤ η` with `t = √(2N) η`, written without square roots. -/
def PermSectorLemmaMatrix : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (s t : Fin N → Perm Ω) (Δ τ : ℝ),
    (∀ i, s i ^ 2 = 1) → (∀ i, t i ^ 2 = 1) → (∀ i, (s i * t i) ^ 3 = 1) →
    0 ≤ Δ → (∀ i, Δ ^ 2 ≤ hs2 (pmat (s i * t i) - 1)) →
    0 ≤ τ →
    (∀ i j, i ≠ j → ∀ k l,
      2 * N * hs2 (pmat (nf (s i) (t i) k) * pmat (nf (s j) (t j) l) -
        pmat (nf (s j) (t j) l) * pmat (nf (s i) (t i) k)) ≤ τ ^ 2) →
    τ ≤ Δ → τ ^ 2 ≤ 5 / 6 →
    N * ((Δ - τ) ^ 2 / 3 - h2 (τ ^ 2) - τ ^ 2 * Real.logb 2 5) ≤ Real.logb 2 (Fintype.card Ω)

/-- The matrix form implies the Hamming form (`‖P_σ - P_π‖₂² = 2 dH σ π`). -/
theorem permSectorLemma_of_matrix (h : PermSectorLemmaMatrix.{u}) : PermSectorLemma.{u} := by
  intro Ω _ _ N s t Δ τ hs ht hst hΔ0 hΔ hτ0 hc hτΔ hτ
  refine h Ω N s t Δ τ hs ht hst hΔ0 (fun i => ?_) hτ0 (fun i j hij k l => ?_) hτΔ hτ
  · rw [hs2_pmat_sub_one]
    exact hΔ i
  · rw [hs2_pmat_comm]
    have := hc i j hij k l
    linarith

/-! ### Numerics -/

lemma log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  have h := Real.add_one_lt_exp (show (-(1 : ℝ) / 2) ≠ 0 by norm_num)
  have h1 : Real.log (1 / 2) < Real.log (Real.exp (-(1 : ℝ) / 2)) :=
    Real.log_lt_log (by norm_num) (by linarith)
  rw [Real.log_exp, one_div, Real.log_inv] at h1
  linarith

/-- The final estimate of the paper (`(Δ-t)²/3 - h₂(t²) - t² log 5 ≥ 1/16`), at the values used below:
`Δ = 1/2`, `t = 1/500` (so `(Δ - t)² ≥ (49/100)²` and `t² < 10⁻⁴`, as in the paper). -/
lemma numeric_sector :
    (1 : ℝ) / 16 ≤ (1 / 2 - 1 / 500) ^ 2 / 3 - h2 ((1 / 500) ^ 2) - (1 / 500) ^ 2 * Real.logb 2 5 := by
  set p : ℝ := (1 / 500) ^ 2 with hp
  clear_value p
  have hpval : p = 1 / 250000 := by rw [hp]; norm_num
  have hl2 := log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  have hp0 : 0 < p := by rw [hpval]; norm_num
  have hp1 : p < 1 := by rw [hpval]; norm_num
  -- `log₂ p ≥ -18`
  have hlogp : -18 ≤ Real.logb 2 p := by
    rw [Real.logb, le_div_iff₀ hl2pos]
    have h := Real.log_le_log (show (0 : ℝ) < ((2 : ℝ) ^ 18)⁻¹ by norm_num)
      (show ((2 : ℝ) ^ 18)⁻¹ ≤ p by rw [hpval]; norm_num)
    rw [Real.log_inv, Real.log_pow] at h
    push_cast at h
    linarith
  -- `-(1-p) log₂ (1-p) ≤ 2p`
  have hq : -((1 - p) * Real.logb 2 (1 - p)) ≤ 2 * p := by
    have h1p : 0 < 1 - p := by linarith
    have hL := Real.log_le_sub_one_of_pos (inv_pos.mpr h1p)
    rw [Real.log_inv] at hL
    have hinv : (1 - p)⁻¹ - 1 = p / (1 - p) := by
      rw [eq_div_iff h1p.ne', sub_mul, inv_mul_cancel₀ h1p.ne', one_mul]
      ring
    rw [hinv] at hL
    have key : (1 - p) * -Real.log (1 - p) ≤ p := by
      have h1p' : 1 - p ≠ 0 := h1p.ne'
      have := mul_le_mul_of_nonneg_left hL h1p.le
      calc (1 - p) * -Real.log (1 - p) ≤ (1 - p) * (p / (1 - p)) := this
        _ = p := by field_simp
    have e : -((1 - p) * Real.logb 2 (1 - p)) = ((1 - p) * -Real.log (1 - p)) / Real.log 2 := by
      rw [Real.logb]
      ring
    rw [e, div_le_iff₀ hl2pos]
    nlinarith
  -- `log₂ 5 ≤ 3`
  have h5 : Real.logb 2 5 ≤ 3 := by
    rw [Real.logb, div_le_iff₀ hl2pos]
    have h := Real.log_le_log (show (0 : ℝ) < 5 by norm_num) (show (5 : ℝ) ≤ 2 ^ 3 by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have m1 := mul_le_mul_of_nonneg_left hlogp hp0.le
  have m2 := mul_le_mul_of_nonneg_left h5 hp0.le
  have hc : ((1 : ℝ) / 2 - 1 / 500) ^ 2 / 3 = 62001 / 750000 := by norm_num
  rw [hc]
  unfold h2
  linarith [m1, m2, hq, hpval]

/-! ### Commuting normal forms -/

section NormalForms

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma dH_single_list_comm (a : Perm Ω) (w' : List (Perm Ω)) (ε : ℝ)
    (h : ∀ b ∈ w', dH (a * b) (b * a) ≤ ε) :
    dH (a * w'.prod) (w'.prod * a) ≤ w'.length * ε := by
  induction w' with
  | nil => simp [dH_self]
  | cons b w' ih =>
    simp only [List.prod_cons, List.length_cons]
    have hb := h b (by simp)
    have ih' := ih (fun b' hb' => h b' (by simp [hb']))
    calc dH (a * (b * w'.prod)) (b * w'.prod * a)
        ≤ dH (a * (b * w'.prod)) (b * a * w'.prod) + dH (b * a * w'.prod) (b * w'.prod * a) :=
          dH_triangle _ _ _
      _ = dH (a * b) (b * a) + dH (a * w'.prod) (w'.prod * a) := by
          congr 1
          · rw [← mul_assoc, dH_mul_right]
          · rw [mul_assoc, mul_assoc, dH_mul_left]
      _ ≤ ε + w'.length * ε := add_le_add hb ih'
      _ = ((w'.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- Interchanging two words costs at most (length × length) single interchanges. -/
lemma dH_list_comm (w w' : List (Perm Ω)) (ε : ℝ)
    (h : ∀ a ∈ w, ∀ b ∈ w', dH (a * b) (b * a) ≤ ε) :
    dH (w.prod * w'.prod) (w'.prod * w.prod) ≤ w.length * w'.length * ε := by
  induction w with
  | nil => simp [dH_self]
  | cons a w ih =>
    simp only [List.prod_cons, List.length_cons]
    have ha := dH_single_list_comm a w' ε (h a (by simp))
    have ih' := ih (fun a' ha' => h a' (by simp [ha']))
    calc dH (a * w.prod * w'.prod) (w'.prod * (a * w.prod))
        ≤ dH (a * w.prod * w'.prod) (a * w'.prod * w.prod) +
            dH (a * w'.prod * w.prod) (w'.prod * (a * w.prod)) := dH_triangle _ _ _
      _ = dH (w.prod * w'.prod) (w'.prod * w.prod) + dH (a * w'.prod) (w'.prod * a) := by
          congr 1
          · rw [mul_assoc, mul_assoc, dH_mul_left]
          · rw [← mul_assoc, dH_mul_right]
      _ ≤ w.length * w'.length * ε + w'.length * ε := add_le_add ih' ha
      _ = ((w.length + 1 : ℕ) : ℝ) * w'.length * ε := by push_cast; ring

/-- Each normal form in `s, t` is within `2 eₛ + eₜ` of a word of length `≤ 3` in `A, B`. -/
lemma nf_close (s t A B : Perm Ω) (es et : ℝ) (hs : dH s A ≤ es) (ht : dH t B ≤ et)
    (k : Fin 6) : ∃ w : List (Perm Ω), w.length ≤ 3 ∧ (∀ x ∈ w, x = A ∨ x = B) ∧
      dH (nf s t k) w.prod ≤ 2 * es + et := by
  have hes : 0 ≤ es := (dH_nonneg _ _).trans hs
  have het : 0 ≤ et := (dH_nonneg _ _).trans ht
  fin_cases k
  · refine ⟨[], by simp, by simp, ?_⟩
    rw [List.prod_nil]
    show dH 1 1 ≤ 2 * es + et
    rw [dH_self]
    linarith
  · refine ⟨[A], by simp, by simp, ?_⟩
    rw [List.prod_cons, List.prod_nil, mul_one]
    show dH s A ≤ 2 * es + et
    linarith
  · refine ⟨[B], by simp, by simp, ?_⟩
    rw [List.prod_cons, List.prod_nil, mul_one]
    show dH t B ≤ 2 * es + et
    linarith
  · refine ⟨[A, B], by simp, by simp, ?_⟩
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    show dH (s * t) (A * B) ≤ 2 * es + et
    have := dH_mul_le s t A B
    linarith
  · refine ⟨[B, A], by simp, by simp, ?_⟩
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    show dH (t * s) (B * A) ≤ 2 * es + et
    have := dH_mul_le t s B A
    linarith
  · refine ⟨[A, B, A], by simp, by simp, ?_⟩
    rw [List.prod_cons, List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
    show dH (s * t * s) (A * (B * A)) ≤ 2 * es + et
    have h1 := dH_mul_le s t A B
    have h2 := dH_mul_le (s * t) s (A * B) A
    rw [← mul_assoc]
    linarith

/-- Two normal forms built from nearby pairs commute up to `|w||w'| ε` plus the rounding errors. -/
lemma nf_comm (si ti Ai Bi sj tj Aj Bj : Perm Ω) (es et ε : ℝ) (hsi : dH si Ai ≤ es)
    (hti : dH ti Bi ≤ et) (hsj : dH sj Aj ≤ es) (htj : dH tj Bj ≤ et) (hε : 0 ≤ ε)
    (hc : ∀ x, x = Ai ∨ x = Bi → ∀ y, y = Aj ∨ y = Bj → dH (x * y) (y * x) ≤ ε) (k l : Fin 6) :
    dH (nf si ti k * nf sj tj l) (nf sj tj l * nf si ti k) ≤ 9 * ε + 4 * (2 * es + et) := by
  obtain ⟨w, hwl, hwm, hwd⟩ := nf_close si ti Ai Bi es et hsi hti k
  obtain ⟨w', hwl', hwm', hwd'⟩ := nf_close sj tj Aj Bj es et hsj htj l
  have hcomm := dH_list_comm w w' ε (fun x hx y hy => hc x (hwm x hx) y (hwm' y hy))
  have hlen : (w.length : ℝ) * w'.length * ε ≤ 9 * ε := by
    have h1 : (w.length : ℝ) ≤ 3 := by exact_mod_cast hwl
    have h2 : (w'.length : ℝ) ≤ 3 := by exact_mod_cast hwl'
    have h3 : (w.length : ℝ) * w'.length ≤ 9 := by
      have := mul_le_mul h1 h2 (Nat.cast_nonneg _) (by norm_num)
      linarith
    nlinarith
  have e1 := dH_mul_le (nf si ti k) (nf sj tj l) w.prod w'.prod
  have e2 := dH_mul_le (nf sj tj l) (nf si ti k) w'.prod w.prod
  rw [dH_comm (nf sj tj l * nf si ti k)] at e2
  have t1 := dH_triangle (nf si ti k * nf sj tj l) (w.prod * w'.prod) (nf sj tj l * nf si ti k)
  have t2 := dH_triangle (w.prod * w'.prod) (w'.prod * w.prod) (nf sj tj l * nf si ti k)
  linarith

end NormalForms

/-- **Proposition `prop:dimension-perm`**, assuming Lemma `lem:sector` for permutation matrices
(Hamming form). -/
theorem dimension_perm_of_sectorLemma (hS : PermSectorLemma.{u}) {Ω : Type u} [Fintype Ω]
    [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N) (hA : AstarLE (3 * N) A)
    (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) := by
  have hδ' : (10 : ℝ) ^ 8 * N * max 1 (A : ℝ) * δ ≤ 1 := by
    simpa [Nat.cast_max] using hδ
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
  -- the exact local `S₃` pairs `s_i = x_i`, `t_i = x_i c_i`
  let s : Fin N → Perm Ω := px φ N
  let t : Fin N → Perm Ω := fun i => px φ N i * pc φ N i
  have hst : ∀ i, s i * t i = pc φ N i := by
    intro i
    show px φ N i * (px φ N i * pc φ N i) = pc φ N i
    rw [← mul_assoc, px, roundInv_mul_self, one_mul]
  have hs2 : ∀ i, s i ^ 2 = 1 := px_sq φ N
  have ht2 : ∀ i, t i ^ 2 = 1 := by
    intro i
    show (px φ N i * pc φ N i) ^ 2 = 1
    rw [pow_two, ← mul_assoc, px_pc_px, inv_mul_cancel]
  have hst3 : ∀ i, (s i * t i) ^ 3 = 1 := fun i => by rw [hst]; exact pc_pow_three φ N i
  have hΔ : ∀ i, (1 / 2 : ℝ) ^ 2 ≤ 2 * dH (s i * t i) 1 := by
    intro i
    rw [hst]
    have := dH_pc_one φ N δ hrel hγ i
    nlinarith
  have hcomm : ∀ i j, i ≠ j → ∀ k l,
      4 * N * dH (nf (s i) (t i) k * nf (s j) (t j) l) (nf (s j) (t j) l * nf (s i) (t i) k)
        ≤ (1 / 500 : ℝ) ^ 2 := by
    intro i j hij k l
    have hb := nf_comm (s i) (t i) (pA φ N i) (pB φ N i) (s j) (t j) (pA φ N j) (pB φ N j)
      δ (8 * δ) (A * δ) (dH_px φ N δ hrel i) (dH_pt φ N δ hrel i) (dH_px φ N δ hrel j)
      (dH_pt φ N δ hrel j) (mul_nonneg (Nat.cast_nonneg _) hδ0) (by
        intro x hx y hy
        have f := far_pairs φ N δ hrel A hA hδ0 i j hij
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · simpa using f true true
        · simpa using f true false
        · simpa using f false true
        · simpa using f false false) k l
    have hd : dH (nf (s i) (t i) k * nf (s j) (t j) l) (nf (s j) (t j) l * nf (s i) (t i) k)
        ≤ 49 * (M * δ) := by
      linarith
    have h4 : 4 * (N : ℝ) * (49 * (M * δ)) ≤ 196 / 10 ^ 8 := by nlinarith
    have hd0 := dH_nonneg (nf (s i) (t i) k * nf (s j) (t j) l) (nf (s j) (t j) l * nf (s i) (t i) k)
    have h5 : 4 * (N : ℝ) * dH (nf (s i) (t i) k * nf (s j) (t j) l)
        (nf (s j) (t j) l * nf (s i) (t i) k) ≤ 4 * (N : ℝ) * (49 * (M * δ)) :=
      mul_le_mul_of_nonneg_left hd (by linarith)
    norm_num at h4 ⊢
    linarith
  have key := hS Ω N s t (1 / 2) (1 / 500) hs2 ht2 hst3 (by norm_num) hΔ (by norm_num) hcomm
    (by norm_num) (by norm_num)
  have hnum := numeric_sector
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  calc (N : ℝ) / 16 = N * (1 / 16) := by ring
    _ ≤ N * ((1 / 2 - 1 / 500) ^ 2 / 3 - h2 ((1 / 500) ^ 2) - (1 / 500) ^ 2 * Real.logb 2 5) :=
        mul_le_mul_of_nonneg_left hnum hN0
    _ ≤ _ := key

/-- **Proposition `prop:dimension-perm`**, assuming Lemma `lem:sector` for permutation matrices
in the paper's matrix language. -/
theorem dimension_perm_of_sectorLemmaMatrix (hS : PermSectorLemmaMatrix.{u}) {Ω : Type u}
    [Fintype Ω] [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ)
    (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N)
    (hA : AstarLE (3 * N) A) (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_sectorLemma (permSectorLemma_of_matrix hS) φ δ hrel hγ N A hN hA hδ

end Houghton
