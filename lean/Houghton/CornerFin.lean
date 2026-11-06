import Houghton.Corner
import Houghton.UpperCheck

/-!
# Section 6: the finite corner models `Ω_{M,s}` as permutation models

`Ω = ℤ/M × ℤ/M × (Fin N → Fin M)` with `N = 6M + 7` (coordinates `0, …, L`, `L = 3ℓ = 6M + 6`;
coordinate `0` is never moved), i.e. `s = M` colours. The generator actions are the ℕ-level
actions of `Corner.lean` restricted along the clamping embedding `ι`. `φ_M : F →* Sym(Ω)` sends
each generator to the inverse of its (right) action, so `φ_M w` is the inverse of the paper's
action of `w`. Relators `r₁, r₂, r₃, r₅` act trivially and `r₄` moves only states at the corner
clock, so `dH (φ_M r_i) 1 ≤ 1/M²`.
-/

namespace Houghton.Corner

open Finset

section fix

/-- `g` fixes every `k ≥ L`. -/
def FixAbove (g : ℕ → ℕ) (L : ℕ) : Prop := ∀ k, L ≤ k → g k = k

theorem cyc_fix {r L : ℕ} (h1 : 1 < L) (h : r < L) : FixAbove (cyc r) L := by
  intro k hk; unfold cyc; split_ifs <;> omega
theorem cycInv_fix {r L : ℕ} (h : r < L) : FixAbove (cycInv r) L := by
  intro k hk; unfold cycInv; split_ifs <;> omega
theorem swp_fix {L : ℕ} (h : 2 < L) : FixAbove (swp 1 2) L := by
  intro k hk; unfold swp; split_ifs <;> omega
theorem D_fix (M i : ℕ) (L : ℕ) (h : 3 * M + 5 < L) : FixAbove (D M i) L := by
  induction i with
  | zero => exact cyc_fix (by omega) (by omega)
  | succ i ih =>
    intro k hk
    simp only [D]
    rw [cycInv_fix (by omega) k hk, swp_fix (by omega) k hk, ih k hk, cyc_fix (by omega) (by omega) k hk]
theorem Dinv_fix (M i : ℕ) (L : ℕ) (h : 3 * M + 5 < L) : FixAbove (Dinv M i) L := by
  induction i with
  | zero => exact cycInv_fix (by omega)
  | succ i ih =>
    intro k hk
    simp only [Dinv]
    rw [cycInv_fix (by omega) k hk, ih k hk, swp_fix (by omega) k hk, cyc_fix (by omega) (by omega) k hk]

/-- Pulling back a clamp-invariant colouring along a map fixing everything above `L`. -/
theorem clamp_pull {S : Type*} {g : ℕ → ℕ} {L : ℕ} (hg : FixAbove g L) {X : ℕ → S}
    (hX : ∀ k, X k = X (min k L)) (k : ℕ) : X (g k) = X (g (min k L)) := by
  rcases le_total k L with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, hg k h, hg L le_rfl, hX k, min_eq_right h]

end fix

variable (M : ℕ) [NeZero M]

/-- Number of coordinates `N = L + 1`, `L = 6M + 6`. -/
def NN : ℕ := 6 * M + 7

/-- The states of the corner model with `s = M` colours. -/
abbrev Ω := ZMod M × ZMod M × (Fin (NN M) → Fin M)

def clampF (k : ℕ) : Fin (NN M) := ⟨min k (6 * M + 6), by unfold NN; omega⟩

/-- The clamping embedding into the ℕ-level model. -/
def iota (ω : Ω M) : CState M (Fin M) := (ω.1, ω.2.1, fun k => ω.2.2 (clampF M k))

/-- Restriction of an ℕ-level state. -/
def res (s : CState M (Fin M)) : Ω M := (s.1, s.2.1, fun t => s.2.2 t.val)

theorem res_iota (ω : Ω M) : res M (iota M ω) = ω := by
  obtain ⟨i, j, x⟩ := ω
  simp only [res, iota, Prod.mk.injEq, true_and]
  funext t
  congr 1; ext; simp only [clampF]; have := t.isLt; unfold NN at this; omega

/-- Clamp-invariant ℕ-level states. -/
def ClampInv (s : CState M (Fin M)) : Prop := ∀ k, s.2.2 k = s.2.2 (min k (6 * M + 6))

theorem iota_clampInv (ω : Ω M) : ClampInv M (iota M ω) := by
  intro k; simp only [iota, clampF, min_assoc, min_self]

theorem iota_res {s : CState M (Fin M)} (hs : ClampInv M s) : iota M (res M s) = s := by
  obtain ⟨i, j, X⟩ := s
  simp only [iota, res, clampF, Prod.mk.injEq, true_and]
  funext k; exact (hs k).symm

/-- The ℕ-level action of a letter. -/
def natActL : Letter → CState M (Fin M) → CState M (Fin M)
  | (⟨0, _⟩, true) => actA M
  | (⟨0, _⟩, false) => actAinv M
  | (⟨1, _⟩, true) => actB M
  | (⟨1, _⟩, false) => actBinv M
  | (_, _) => actα M

theorem ell_le (i j : ZMod M) : ell M - i.val - j.val ≤ 2 * M + 2 := by unfold ell; omega

theorem natActL_clampInv (hM : 2 ≤ M) (l : Letter) {s : CState M (Fin M)} (hs : ClampInv M s) :
    ClampInv M (natActL M l s) := by
  obtain ⟨i, j, X⟩ := s
  have hr := ell_sub_ge M i j
  obtain ⟨⟨_ | _ | _ | n, hn⟩, _ | _⟩ := l
  all_goals first
    | omega
    | (intro k; simp only [natActL, actA, actAinv, actB, actBinv, actα])
  · exact clamp_pull (cyc_fix (by omega) (by have := ell_le M (i - 1) j; omega)) hs k
  · exact clamp_pull (cycInv_fix (by have := ell_le M i j; omega)) hs k
  · apply clamp_pull _ hs k
    unfold Bfwd; split_ifs
    · exact cyc_fix (by omega) (by unfold ell; omega)
    · exact D_fix M _ _ (by omega)
  · apply clamp_pull _ hs k
    unfold Binv; split_ifs
    · exact cycInv_fix (by unfold ell; omega)
    · exact Dinv_fix M _ _ (by omega)
  · exact clamp_pull (swp_fix (by omega)) hs k
  · exact clamp_pull (swp_fix (by omega)) hs k

/-- The finite action of a letter. -/
def finActL (l : Letter) (ω : Ω M) : Ω M := res M (natActL M l (iota M ω))

theorem iota_finActL (hM : 2 ≤ M) (l : Letter) (ω : Ω M) :
    iota M (finActL M l ω) = natActL M l (iota M ω) :=
  iota_res M (natActL_clampInv M hM l (iota_clampInv M ω))

theorem Binv_Bfwd (hM : 2 ≤ M) (i j : ZMod M) (t : ℕ) : Binv M i j (Bfwd M i j t) = t := by
  have := ZMod.val_lt i; have := ZMod.val_lt j
  unfold Binv Bfwd; split_ifs
  · exact cycInv_cyc _ _ (by unfold ell; omega)
  · exact Dinv_D M hM _ (by omega) _

theorem Bfwd_Binv (hM : 2 ≤ M) (i j : ZMod M) (t : ℕ) : Bfwd M i j (Binv M i j t) = t := by
  have := ZMod.val_lt i; have := ZMod.val_lt j
  unfold Binv Bfwd; split_ifs
  · exact cyc_cycInv _ _ (by unfold ell; omega)
  · exact D_Dinv M hM _ (by omega) _

theorem natActL_inv (hM : 2 ≤ M) (i : Fin 3) (b : Bool) (s : CState M (Fin M)) :
    natActL M (i, !b) (natActL M (i, b) s) = s := by
  obtain ⟨i', j, X⟩ := s
  obtain ⟨_ | _ | _ | n, hn⟩ := i
  · cases b
    · simp only [Bool.not_false, natActL, actA, actAinv, sub_add_cancel, Prod.mk.injEq, true_and]
      funext t; rw [cyc_cycInv _ _ (by have := ell_sub_ge M (i' - 1) j; omega)]
    · simp only [Bool.not_true, natActL, actA, actAinv, add_sub_cancel_right, Prod.mk.injEq,
        true_and]
      funext t; rw [cycInv_cyc _ _ (by have := ell_sub_ge M i' j; omega)]
  · cases b
    · simp only [Bool.not_false, natActL, actB, actBinv, sub_add_cancel, Prod.mk.injEq, true_and]
      funext t; rw [Bfwd_Binv M hM]
    · simp only [Bool.not_true, natActL, actB, actBinv, add_sub_cancel_right, Prod.mk.injEq,
        true_and]
      funext t; rw [Binv_Bfwd M hM]
  · cases b <;> exact r1_trivial M _
  · omega

theorem finActL_inv (hM : 2 ≤ M) (i : Fin 3) (b : Bool) (ω : Ω M) :
    finActL M (i, !b) (finActL M (i, b) ω) = ω := by
  have h := iota_finActL M hM (i, b) ω
  unfold finActL at h ⊢
  rw [h, natActL_inv M hM, res_iota]

/-- The paper's (right) action of generator `i` as a permutation. -/
def genP (hM : 2 ≤ M) (i : Fin 3) : Equiv.Perm (Ω M) where
  toFun := finActL M (i, true)
  invFun := finActL M (i, false)
  left_inv ω := finActL_inv M hM i true ω
  right_inv ω := finActL_inv M hM i false ω

/-- The corner model `φ_M : F →* Sym(Ω)` (generators act by the inverses of the paper's
right actions). -/
def phiC (hM : 2 ≤ M) : F →* Equiv.Perm (Ω M) := FreeGroup.lift fun i => (genP M hM i)⁻¹

/-- The paper's action of a coded word (first letter first). -/
def natNest : List ℕ → CState M (Fin M) → CState M (Fin M)
  | [], s => s
  | c :: w, s => natNest w (natActL M (codeLetter c) s)

def finNest : List ℕ → Ω M → Ω M
  | [], ω => ω
  | c :: w, ω => finNest w (finActL M (codeLetter c) ω)

theorem iota_finNest (hM : 2 ≤ M) (w : List ℕ) (ω : Ω M) :
    iota M (finNest M w ω) = natNest M w (iota M ω) := by
  induction w generalizing ω with
  | nil => rfl
  | cons c w ih => simp only [finNest, natNest, ih, iota_finActL M hM]

theorem finNest_eq (hM : 2 ≤ M) (w : List ℕ) (ω : Ω M) :
    finNest M w ω = res M (natNest M w (iota M ω)) := by
  rw [← iota_finNest M hM, res_iota]

theorem genP_letter (hM : 2 ≤ M) (c : ℕ) (ω : Ω M) :
    ((phiC M hM (ltr c))⁻¹ : Equiv.Perm (Ω M)) ω = finActL M (codeLetter c) ω := by
  unfold ltr genN codeLetter
  by_cases h : c % 2 = 0
  · simp [h, phiC, FreeGroup.lift_apply_of, genP]
  · have h' : (c % 2 == 0) = false := by simpa using h
    simp [h, h', phiC, FreeGroup.lift_apply_of, genP]

/-- `φ_M (ev w)⁻¹` is the paper's action of `w`. -/
theorem phiC_ev_inv_apply (hM : 2 ≤ M) (w : List ℕ) (ω : Ω M) :
    ((phiC M hM (ev w))⁻¹ : Equiv.Perm (Ω M)) ω = finNest M w ω := by
  induction w generalizing ω with
  | nil => simp [ev, finNest]
  | cons c w ih =>
    have : ev (c :: w) = ltr c * ev w := by simp [ev]
    rw [this, map_mul, mul_inv_rev, Equiv.Perm.mul_apply, genP_letter, ih]
    rfl


/-! ### Relator defects -/

theorem natNest_rel_off (hM : 2 ≤ M) (k : ℕ) (hk : k < 5) (s : CState M (Fin M))
    (hc : ¬ (s.1.val = M - 1 ∧ s.2.1.val = M - 1)) : natNest M (Word.relW k) s = s := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · exact r1_trivial M s
  · exact r2_trivial M s
  · exact r3_trivial M s
  · exact r4_trivial_off_corner M hM s hc
  · exact r5_trivial M hM s

theorem natNest_rel (hM : 2 ≤ M) (k : ℕ) (hk : k < 5) (hk3 : k ≠ 3) (s : CState M (Fin M)) :
    natNest M (Word.relW k) s = s := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4) with rfl | rfl | rfl | rfl
  · exact r1_trivial M s
  · exact r2_trivial M s
  · exact r3_trivial M s
  · exact r5_trivial M hM s

theorem card_Ω : Fintype.card (Ω M) = M * (M * M ^ NN M) := by
  simp [Ω, Fintype.card_prod, ZMod.card]

/-- The corner clock. -/
def cornerC : ZMod M := ((M - 1 : ℕ) : ZMod M)

theorem eq_cornerC {i : ZMod M} (h : i.val = M - 1) : i = cornerC M := by
  apply ZMod.val_injective
  rw [h, cornerC, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := NeZero.ne M; omega)]

theorem div_bound (c : ℕ) (hc : c ≤ M ^ NN M) :
    (c : ℝ) / ((M * (M * M ^ NN M) : ℕ) : ℝ) ≤ 1 / (M : ℝ) ^ 2 := by
  have hMpos : (0 : ℝ) < M := by have := NeZero.ne M; exact_mod_cast Nat.pos_of_ne_zero this
  have hpow : (0 : ℝ) < (M : ℝ) ^ NN M := by positivity
  have hc' : (c : ℝ) ≤ (M : ℝ) ^ NN M := by exact_mod_cast hc
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Relator defects of the corner models**: `dH (φ_M r_i) 1 ≤ 1/M²`. -/
theorem phiC_rel_le (hM : 2 ≤ M) (i : Fin 5) : dH (phiC M hM (rel i)) 1 ≤ 1 / (M : ℝ) ^ 2 := by
  have hrel : rel i = ev (Word.relW i.val) := by
    rw [ev_relW]; congr 1; ext; simp [idx]; omega
  rw [← ham_inv, inv_one, hrel]
  unfold dH
  have hsub : (univ.filter fun ω => (phiC M hM (ev (Word.relW i.val)))⁻¹ ω ≠ (1 : Equiv.Perm (Ω M)) ω) ⊆
      univ.image (fun x : Fin (NN M) → Fin M => (cornerC M, cornerC M, x)) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and, Equiv.Perm.one_apply, phiC_ev_inv_apply,
      finNest_eq M hM] at hω
    by_cases hc : ω.1.val = M - 1 ∧ ω.2.1.val = M - 1
    · obtain ⟨i', j', x⟩ := ω
      simp only [mem_image, mem_univ, true_and]
      simp only at hc
      exact ⟨x, by rw [eq_cornerC M hc.1, eq_cornerC M hc.2]⟩
    · exfalso; apply hω
      rw [natNest_rel_off M hM _ i.isLt _ hc, res_iota]
  have hcard := (card_le_card hsub).trans card_image_le
  simp only [card_univ, Fintype.card_fun, Fintype.card_fin] at hcard
  rw [card_Ω]
  exact div_bound M _ hcard

end Houghton.Corner
