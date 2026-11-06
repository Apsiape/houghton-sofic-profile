import Houghton.Area.Certificates
import Houghton.Area.Checks107

/-! Weighted area in the auxiliary presentation: `WAreaLE w n` (total weight `≤ n`), its
algebra, soundness of the auxiliary checker, domination `WAreaLE → AreaLE` (`r₆` costs `B(2) = 9`),
and transport through `D = ψ` (`M w ≤ 107 w`). -/

namespace Houghton

open Word

/-- The auxiliary relators. -/
def relA : ℕ → F
  | 0 => r₁
  | 1 => r₃
  | 2 => r₄
  | 3 => r₅
  | _ => comm (σneg 2) b

/-- An auxiliary cell. -/
def cellA (c : F × ℕ × Bool) : F :=
  c.1 * (if c.2.2 then relA c.2.1 else (relA c.2.1)⁻¹) * c.1⁻¹

/-- Weighted area at most `n` in the auxiliary presentation. -/
def WAreaLE (w : F) (n : ℕ) : Prop :=
  ∃ cs : List (F × ℕ × Bool), (cs.map fun c => wtA c.2.1).sum ≤ n ∧ (cs.map cellA).prod = w

lemma ev_qW : ev qW = σneg 2 := by simp [qW, σneg, pow_two, mul_assoc]

lemma ev_relWA (i : ℕ) : ev (relWA i) = relA i := by
  rcases i with _ | _ | _ | _ | i
  · rw [show relWA 0 = relW 0 from rfl, ev_relW]; rfl
  · rw [show relWA 1 = relW 2 from rfl, ev_relW]; rfl
  · rw [show relWA 2 = relW 3 from rfl, ev_relW]; rfl
  · rw [show relWA 3 = relW 4 from rfl, ev_relW]; rfl
  · rw [show relWA (i + 1 + 1 + 1 + 1) = r6W from rfl, r6W, ev_commW, ev_qW]
    simp [relA]

/-! ### Soundness of the auxiliary checker -/

lemma wsum_decode (data : List ℕ) :
    (((data.map decodeCell).map toGCell).map fun c => wtA c.2.1).sum = wsumA data := by
  induction data with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

/-- **Soundness of the auxiliary checker.** -/
theorem checkPackedA_sound (data target : List ℕ) (h : checkPacked relWA data target = true) :
    WAreaLE (ev target) (wsumA data) :=
  ⟨(data.map decodeCell).map toGCell, (wsum_decode data).le,
    checkPacked_prod relWA relA ev_relWA data target h⟩

/-! ### Algebra -/

lemma WAreaLE.mono {w : F} {n m : ℕ} (h : WAreaLE w n) (hnm : n ≤ m) : WAreaLE w m := by
  obtain ⟨cs, hl, hp⟩ := h
  exact ⟨cs, hl.trans hnm, hp⟩

lemma WAreaLE.one : WAreaLE 1 0 := ⟨[], le_rfl, by simp⟩

lemma WAreaLE.of_eq {w w' : F} {n : ℕ} (h : WAreaLE w n) (e : w = w') : WAreaLE w' n := e ▸ h

lemma WAreaLE.of_eq_one {w : F} (e : w = 1) : WAreaLE w 0 := WAreaLE.one.of_eq e.symm

lemma WAreaLE.mul {u v : F} {n m : ℕ} (hu : WAreaLE u n) (hv : WAreaLE v m) :
    WAreaLE (u * v) (n + m) := by
  obtain ⟨cs, hl, hp⟩ := hu
  obtain ⟨ds, hl', hp'⟩ := hv
  exact ⟨cs ++ ds, by simp [List.sum_append]; omega, by simp [List.prod_append, hp, hp']⟩

lemma WAreaLE.conj {w : F} {n : ℕ} (g : F) (h : WAreaLE w n) : WAreaLE (g * w * g⁻¹) n := by
  obtain ⟨cs, hl, hp⟩ := h
  refine ⟨cs.map fun c => (g * c.1, c.2), by simpa [Function.comp_def] using hl, ?_⟩
  have : (cs.map fun c => (g * c.1, c.2)).map cellA = (cs.map cellA).map (fun x => g * x * g⁻¹) := by
    simp only [List.map_map, Function.comp_def]
    congr 1
    funext c
    rcases c with ⟨z, i, s⟩
    cases s <;> simp [cellA, mul_assoc, mul_inv_rev]
  rw [this, prod_map_conj, hp]

lemma WAreaLE.inv {w : F} {n : ℕ} (h : WAreaLE w n) : WAreaLE w⁻¹ n := by
  obtain ⟨cs, hl, hp⟩ := h
  refine ⟨(cs.map fun c => (c.1, c.2.1, !c.2.2)).reverse, by simpa [Function.comp_def] using hl, ?_⟩
  rw [← hp, prod_inv_reverse']
  simp only [List.map_reverse, List.map_map, Function.comp_def]
  congr 2
  exact List.map_congr_left (fun (c : F × ℕ × Bool) _ => by
    rcases c with ⟨z, i, s⟩
    cases s <;> simp [cellA, mul_assoc])

/-- `u = v` modulo weight `n`. -/
def WAreaEq (u v : F) (n : ℕ) : Prop := WAreaLE (u * v⁻¹) n

lemma WAreaEq.mono {u v : F} {n m : ℕ} (h : WAreaEq u v n) (hnm : n ≤ m) : WAreaEq u v m :=
  WAreaLE.mono h hnm

lemma WAreaEq.of_eq {u v : F} (h : u = v) : WAreaEq u v 0 := WAreaLE.of_eq_one (by simp [h])

lemma WAreaEq.refl (u : F) : WAreaEq u u 0 := WAreaEq.of_eq rfl

lemma WAreaEq.trans {u v w : F} {n m : ℕ} (h₁ : WAreaEq u v n) (h₂ : WAreaEq v w m) :
    WAreaEq u w (n + m) :=
  (WAreaLE.mul h₁ h₂).of_eq (by simp [mul_assoc])

lemma WAreaEq.mul {u v u' v' : F} {n m : ℕ} (h₁ : WAreaEq u v n) (h₂ : WAreaEq u' v' m) :
    WAreaEq (u * u') (v * v') (n + m) := by
  have := WAreaLE.mul (WAreaLE.conj u h₂) h₁
  rw [Nat.add_comm]
  exact this.of_eq (by simp [mul_assoc, mul_inv_rev])

lemma WAreaEq.inv {u v : F} {n : ℕ} (h : WAreaEq u v n) : WAreaEq u⁻¹ v⁻¹ n :=
  (WAreaLE.conj u⁻¹ (WAreaLE.inv h)).of_eq (by simp [mul_assoc, mul_inv_rev])

lemma WAreaEq.conj {u v : F} {n : ℕ} (g : F) (h : WAreaEq u v n) :
    WAreaEq (g * u * g⁻¹) (g * v * g⁻¹) n :=
  (WAreaLE.conj g h).of_eq (by simp [mul_assoc, mul_inv_rev])

/-! ### Domination: weighted area bounds the original area -/

lemma AreaLE.cellA (c : F × ℕ × Bool) : AreaLE (cellA c) (wtA c.2.1) := by
  rcases c with ⟨z, i, s⟩
  have hr : AreaLE (relA i) (wtA i) := by
    rcases i with _ | _ | _ | _ | i
    · exact (AreaLE.rel 0).mono (by decide)
    · exact (AreaLE.rel 2).mono (by decide)
    · exact (AreaLE.rel 3).mono (by decide)
    · exact (AreaLE.rel 4).mono (by decide)
    · exact area_B2.mono (by simp [wtA])
  cases s
  · simpa [Houghton.cellA] using hr.inv.conj z
  · simpa [Houghton.cellA] using hr.conj z

theorem WAreaLE.toAreaLE {w : F} {n : ℕ} (h : WAreaLE w n) : AreaLE w n := by
  obtain ⟨cs, hl, rfl⟩ := h
  refine AreaLE.mono ?_ hl
  clear hl
  induction cs with
  | nil => simpa using AreaLE.one
  | cons c cs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (AreaLE.cellA c).mul ih

lemma WAreaEq.toAreaEq {u v : F} {n : ℕ} (h : WAreaEq u v n) : AreaEq u v n :=
  WAreaLE.toAreaLE h

/-! ### Transport through `D = ψ` (the substitution matrix, `M w ≤ 107 w`) -/

lemma areaW_of_check {D target : List ℕ} {w : F} {n : ℕ} (h : checkPacked relWA D target = true)
    (hw : ev target = w) (hn : wsumA D ≤ n) : WAreaLE w n :=
  ((checkPackedA_sound D target h).mono hn).of_eq hw

lemma psi_relA_eq (k : ℕ) : ψ (relA k) = ev (psiW (relWA k)) := by
  rw [← ev_relWA]
  exact ψ_ev _ (by
    intro x hx
    rcases k with _ | _ | _ | _ | k <;> simp [relWA, relW, r6W, commW, qW, invW, Word.inv] at hx <;>
      omega)

theorem warea_psi_relA (i : ℕ) : WAreaLE (ψ (relA i)) (107 * wtA i) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := wsum_D
  rcases i with _ | _ | _ | _ | i
  · exact areaW_of_check chk_wD1 (psi_rel_eq' 0) h0
  · exact areaW_of_check chk_wD3 (psi_rel_eq' 1) h1
  · exact areaW_of_check chk_wD4 (psi_rel_eq' 2) h2
  · exact areaW_of_check chk_wD5 (psi_rel_eq' 3) h3
  · have e : relA (i + 1 + 1 + 1 + 1) = relA 4 := rfl
    have e' : wtA (i + 1 + 1 + 1 + 1) = wtA 4 := rfl
    rw [e, e']
    exact areaW_of_check chk_wD6 (psi_rel_eq' 4) h4
where
  psi_rel_eq' (k : ℕ) : ev (psiW (relWA k)) = ψ (relA k) := (psi_relA_eq k).symm

/-- **Weighted transport**: `D(w)` has weighted area at most `107` times that of `w`. -/
theorem WAreaLE.psi {w : F} {n : ℕ} (h : WAreaLE w n) : WAreaLE (ψ w) (107 * n) := by
  obtain ⟨cs, hl, rfl⟩ := h
  refine WAreaLE.mono ?_ (Nat.mul_le_mul_left 107 hl)
  clear hl
  induction cs with
  | nil => simpa using WAreaLE.one
  | cons c cs ih =>
    have hc : WAreaLE (ψ (cellA c)) (107 * wtA c.2.1) := by
      rcases c with ⟨z, i, s⟩
      cases s
      · simpa [Houghton.cellA, map_mul, map_inv] using (warea_psi_relA i).inv.conj (ψ z)
      · simpa [Houghton.cellA, map_mul, map_inv] using (warea_psi_relA i).conj (ψ z)
    simp only [List.map_cons, List.prod_cons, map_mul, List.sum_cons, Nat.mul_add]
    exact hc.mul ih

end Houghton
