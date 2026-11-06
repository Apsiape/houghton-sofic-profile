import Houghton.ShortWord
import Houghton.Main

/-!
# The upper bound of Theorem 1.1 (Proposition `prop:sofic-upper`)

`σ_{E_H}(r) ≤ 2^{7000 √r log₂ r}` for `r ≥ 2`. The model is the diagonal action on two copies of
the corner model `Ω_{M,M}` with `M = ⌈81 √r⌉`; `f(g) = Φ(c_g)` for the canonical word `c_g` of
`g ∈ E_H`. Chunk relations have fillings with `≤ 4` cells (kernel-checked, `UpperCheck`), so their
defect is `≤ 4 · 2/M² ≤ 1/r`; distinct elements differ by a word of length `≤ 20`, which fixes a
fraction `≤ 81/M` of each copy, so `≤ (81/M)² ≤ 1/r` of the product.
-/

namespace Houghton

open Finset

section ham

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem ham_conj (A B : Equiv.Perm Ω) : dH (A * B * A⁻¹) 1 = dH B 1 := by
  rw [← ham_mul_left A⁻¹, ← ham_mul_right _ _ A]; simp [mul_assoc]

theorem ham_mul_le (A B : Equiv.Perm Ω) : dH (A * B) 1 ≤ dH A 1 + dH B 1 := by
  have h1 := ham_triangle (A * B) B 1
  have h2 := ham_mul_right A 1 B
  rw [one_mul] at h2
  linarith

theorem ham_cell_le (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ)
    (c : F × Fin 5 × Bool) : dH (φ (cell c)) 1 ≤ δ := by
  unfold cell
  rw [map_mul, map_mul, map_inv, ham_conj]
  split_ifs
  · exact hrel _
  · rw [map_inv, ← ham_inv, inv_inv, inv_one]; exact hrel _

theorem ham_area (φ : F →* Equiv.Perm Ω) (δ : ℝ) (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hδ : 0 ≤ δ)
    {w : F} {n : ℕ} (h : AreaLE w n) : dH (φ w) 1 ≤ n * δ := by
  obtain ⟨cs, hlen, rfl⟩ := h
  have : ∀ cs : List (F × Fin 5 × Bool), dH (φ (cs.map cell).prod) 1 ≤ cs.length * δ := by
    intro cs
    induction cs with
    | nil => simp [ham_self]
    | cons c cs ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, List.length_cons]
      have := ham_mul_le (φ (cell c)) (φ (cs.map cell).prod)
      have := ham_cell_le φ δ hrel c
      push_cast; linarith
  exact (this cs).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hδ)

/-- Number of agreement points. -/
def agreeC (g h : Equiv.Perm Ω) : ℕ := (univ.filter fun x => g x = h x).card

theorem dH_eq_agree [Nonempty Ω] (g h : Equiv.Perm Ω) :
    dH g h = 1 - (agreeC g h : ℝ) / Fintype.card Ω := by
  have hpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset Ω)) (fun x => g x = h x)
  rw [card_univ] at hsum
  unfold dH agreeC
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos.ne']
  have : (univ.filter fun x => g x ≠ h x).card + (univ.filter fun x => g x = h x).card =
      Fintype.card Ω := by rw [add_comm]; exact hsum
  exact_mod_cast this

/-- The diagonal action on two copies. -/
def diagP : Equiv.Perm Ω →* Equiv.Perm (Ω × Ω) where
  toFun g := Equiv.prodCongr g g
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

theorem agree_diag (g h : Equiv.Perm Ω) : agreeC (diagP g) (diagP h) = agreeC g h ^ 2 := by
  unfold agreeC
  have : (univ.filter fun x : Ω × Ω => diagP g x = diagP h x) =
      (univ.filter fun x => g x = h x) ×ˢ (univ.filter fun x => g x = h x) := by
    ext ⟨x, y⟩
    simp [diagP, Prod.ext_iff]
  rw [this, card_product, sq]

theorem dH_diag [Nonempty Ω] (g h : Equiv.Perm Ω) :
    dH (diagP g) (diagP h) = 1 - (1 - dH g h) ^ 2 := by
  rw [dH_eq_agree, dH_eq_agree, agree_diag, Fintype.card_prod]
  push_cast; ring

theorem dH_diag_le [Nonempty Ω] (g h : Equiv.Perm Ω) : dH (diagP g) (diagP h) ≤ 2 * dH g h := by
  rw [dH_diag]
  have := ham_nonneg g h
  nlinarith

theorem ham_permCongr {n : ℕ} (e : Ω ≃ Fin n) (g h : Equiv.Perm Ω) :
    dH (e.permCongr g) (e.permCongr h) = dH g h := by
  unfold dH
  have hc : Fintype.card (Fin n) = Fintype.card Ω := (Fintype.card_congr e).symm
  rw [hc]
  congr 2
  symm
  apply card_equiv e
  intro x
  simp [Equiv.permCongr_apply]

end ham

/-! ### Soundness of the kernel checks -/

open Word UpperData

theorem fp_spec : ∀ k < 40, fpd k = fpW (cwi k) := by
  have h := chkFp_eq
  simp only [chkFp, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem inj_spec : ∀ k < 40, ∀ k' < 40, fpd k = fpd k' → k = k' := by
  have h := chkInj_eq
  simp only [chkInj, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq] at h
  intro k hk k' hk' he
  rcases h k hk k' hk' with h | h
  · exact absurd he h
  · exact h

theorem len_spec : ∀ k < 40, (cwi k).length ≤ 10 := by
  have h := chkLen_eq
  simp only [chkLen, List.all_eq_true, List.mem_range, Nat.ble_eq] at h
  exact h

theorem lookupK_some {f : List ℕ} {k : ℕ} (h : lookupK f = some k) : k < 40 ∧ fpd k = f := by
  unfold lookupK at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [beq_iff_eq, List.mem_range] at h1 h2
  exact ⟨h2, h1⟩

theorem lookupK_isSome {f : List ℕ} {k : ℕ} (hk : k < 40) (h : fpd k = f) :
    ∃ k', lookupK f = some k' := by
  unfold lookupK
  cases hf : (List.range 40).find? (fun k => fpd k == f) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using h) (hf k (List.mem_range.mpr hk))
  | some k' => exact ⟨k', rfl⟩

theorem fill_spec : ∀ i < 40, ∀ j < 40, ∀ k, lookupK (fpW (cwi i ++ cwi j)) = some k →
    AreaLE (ev (cwi i ++ cwi j ++ invW (cwi k))) 4 := by
  have h := chkFill_eq
  simp only [chkFill, List.all_eq_true, List.mem_range] at h
  intro i hi j hj k hk
  have h' := h i hi j hj
  rw [hk] at h'
  simp only [Bool.and_eq_true, Nat.ble_eq] at h'
  obtain ⟨cs, hl, he⟩ := checkPacked_sound _ _ h'.1
  exact ⟨cs, hl.trans h'.2, he⟩

theorem rho'_of_areaLE {w : F} {n : ℕ} (h : AreaLE w n) : ρH' w = 1 := by
  obtain ⟨cs, -, rfl⟩ := h
  rw [map_list_prod, List.map_map]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
  simp only [Function.comp, cell, map_mul, map_inv]
  split_ifs <;> simp [rho'_rel]

theorem codeLetter_letterCode (l : Letter) : codeLetter (letterCode l) = l := by
  obtain ⟨⟨i, hi⟩, b⟩ := l
  unfold codeLetter letterCode
  cases b <;> refine Prod.ext (Fin.ext ?_) ?_ <;> simp <;> omega

theorem ev_letterCode (w : List Letter) : ev (w.map letterCode) = wordF w := by
  rw [Corner.ev_eq_wordF, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left; intro l _; exact codeLetter_letterCode l

theorem cov_spec (w : List Letter) (hw : w ∈ chunkWords) :
    (∃ k < 40, ρH' (wordF w) = ρH' (ev (cwi k))) ∧
      (∃ k < 40, (ρH' (wordF w))⁻¹ = ρH' (ev (cwi k))) := by
  have h1 := chkCovWords_eq
  simp only [chkCovWords, List.all_eq_true, List.contains_iff_mem, List.mem_map] at h1
  obtain ⟨e, he, hee⟩ := h1 w hw
  have h2 := chkCov_eq
  simp only [chkCov, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at h2
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h2 e he
  have r1 := rho'_of_areaLE (checkPacked_sound _ _ a2)
  have r2 := rho'_of_areaLE (checkPacked_sound _ _ a4)
  rw [ev_append, ev_invW, map_mul, map_inv, mul_inv_eq_one, hee, ev_letterCode] at r1
  rw [ev_append, ev_invW, ev_invW, map_mul, map_inv, map_inv, mul_inv_eq_one, hee,
    ev_letterCode] at r2
  exact ⟨⟨_, a1, r1⟩, ⟨_, a3, r2⟩⟩

theorem E_H_canon {x : H3} (hx : x ∈ E_H) : ∃ k < 40, ρH' (ev (cwi k)) = x := by
  classical
  unfold E_H at hx
  rcases mem_union.mp hx with h | h
  · rw [List.mem_toFinset] at h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    obtain ⟨k, hk, e⟩ := (cov_spec w hw).1
    exact ⟨k, hk, e.symm⟩
  · rw [List.mem_toFinset] at h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    obtain ⟨k, hk, e⟩ := (cov_spec w hw).2
    exact ⟨k, hk, e.symm⟩

/-- The canonical index of an element of `E_H` (`0` elsewhere). -/
noncomputable def cidx (g : H3) : ℕ := by
  classical
  exact if h : ∃ k, k < 40 ∧ ρH' (ev (cwi k)) = g then Nat.find h else 0

theorem cidx_spec {g : H3} (hg : g ∈ E_H) : cidx g < 40 ∧ ρH' (ev (cwi (cidx g))) = g := by
  classical
  have h : ∃ k, k < 40 ∧ ρH' (ev (cwi k)) = g := by
    obtain ⟨k, hk, e⟩ := E_H_canon hg; exact ⟨k, hk, e⟩
  unfold cidx
  rw [dif_pos h]
  exact Nat.find_spec h

theorem cidx_one : cidx 1 = 0 := by
  classical
  have h : ∃ k, k < 40 ∧ ρH' (ev (cwi k)) = 1 := ⟨0, by decide, by
    show ρH' (ev []) = 1; simp [ev]⟩
  unfold cidx
  rw [dif_pos h]
  exact Nat.le_zero.mp (Nat.find_min' h ⟨by decide, by show ρH' (ev []) = 1; simp [ev]⟩)

theorem fpW_eq {u v : List ℕ} (h : ρH (ev u) = ρH (ev v)) : fpW u = fpW v := by
  unfold fpW
  apply List.map_congr_left
  intro p _
  rw [Corner.wActC_eq, Corner.wActC_eq, h]

/-- Every chunk relation `x y = z` has a filling of `c_x c_y c_z⁻¹` with at most 4 cells. -/
theorem chunk_rel_area {x y : H3} (hx : x ∈ E_H) (hy : y ∈ E_H) (hxy : x * y ∈ E_H) :
    AreaLE (ev (cwi (cidx x)) * ev (cwi (cidx y)) * (ev (cwi (cidx (x * y))))⁻¹) 4 := by
  obtain ⟨i1, e1⟩ := cidx_spec hx
  obtain ⟨j1, e2⟩ := cidx_spec hy
  obtain ⟨k1, e3⟩ := cidx_spec hxy
  have hrho : ρH (ev (cwi (cidx x) ++ cwi (cidx y))) = ρH (ev (cwi (cidx (x * y)))) := by
    have : ρH' (ev (cwi (cidx x) ++ cwi (cidx y))) = ρH' (ev (cwi (cidx (x * y)))) := by
      rw [ev_append, map_mul, e1, e2, e3]
    exact congrArg Subtype.val this
  have hfp := fpW_eq hrho
  obtain ⟨k', hk'⟩ := lookupK_isSome k1 ((fp_spec _ k1).trans hfp.symm)
  obtain ⟨hk'1, hk'2⟩ := lookupK_some hk'
  have : k' = cidx (x * y) := inj_spec _ hk'1 _ k1 (by rw [hk'2, hfp, fp_spec _ k1])
  subst this
  have := fill_spec _ i1 _ j1 _ hk'
  rwa [ev_append, ev_append, ev_invW] at this

/-- Distinct elements of `E_H` differ by a word of length `≤ 20` representing a nonidentity
element. -/
theorem chunk_sep {x y : H3} (hx : x ∈ E_H) (hy : y ∈ E_H) (hne : x ≠ y) :
    (invW (cwi (cidx y)) ++ cwi (cidx x)).length ≤ 20 ∧
      ρH (ev (invW (cwi (cidx y)) ++ cwi (cidx x))) ≠ 1 := by
  obtain ⟨i1, e1⟩ := cidx_spec hx
  obtain ⟨j1, e2⟩ := cidx_spec hy
  refine ⟨?_, ?_⟩
  · have := len_spec _ i1; have := len_spec _ j1
    simp [invW]; omega
  · intro h
    apply hne
    rw [← e1, ← e2]
    apply Subtype.ext
    rw [ev_append, ev_invW, map_mul, map_inv, inv_mul_eq_one] at h
    exact h.symm


/-! ### The product model -/

section model

open Corner

variable (M : ℕ) [NeZero M]

instance : Nonempty (Ω M) := ⟨(0, 0, fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩)⟩

/-- The product model `Φ = diag ∘ φ_M` on `Ω × Ω`. -/
noncomputable def PhiP (hM : 2 ≤ M) : F →* Equiv.Perm (Ω M × Ω M) := diagP.comp (phiC M hM)

theorem PhiP_rel (hM : 2 ≤ M) (i : Fin 5) : dH (PhiP M hM (rel i)) 1 ≤ 2 / (M : ℝ) ^ 2 := by
  have h := dH_diag_le (phiC M hM (rel i)) 1
  rw [map_one] at h
  have := phiC_rel_le M hM i
  simp only [PhiP, MonoidHom.comp_apply]
  calc _ ≤ 2 * dH (phiC M hM (rel i)) 1 := h
    _ ≤ 2 * (1 / (M : ℝ) ^ 2) := by linarith
    _ = 2 / (M : ℝ) ^ 2 := by ring

theorem PhiP_area (hM : 2 ≤ M) {w : F} {n : ℕ} (h : AreaLE w n) :
    dH (PhiP M hM w) 1 ≤ n * (2 / (M : ℝ) ^ 2) :=
  ham_area _ _ (PhiP_rel M hM) (by positivity) h

theorem PhiP_sep (hM : 2 ≤ M) (u : List ℕ) (m : ℕ) (hlen : u.length ≤ m) (h2m : 2 * m < M)
    (hne : ρH (ev u) ≠ 1) : 1 - ((4 * m + 1) / (M : ℝ)) ^ 2 ≤ dH (PhiP M hM (ev u)) 1 := by
  simp only [PhiP, MonoidHom.comp_apply]
  rw [← map_one diagP, dH_diag, dH_eq_agree]
  have hfix := fixed_card_le M hM u m hlen h2m hne
  have hag : agreeC (phiC M hM (ev u)) 1 =
      (univ.filter fun ω => finNest M u ω = ω).card := by
    have hset : (univ.filter fun x => (phiC M hM (ev u)) x = (1 : Equiv.Perm (Ω M)) x) =
        univ.filter fun ω => finNest M u ω = ω := by
      apply Finset.filter_congr
      intro ω _
      rw [Equiv.Perm.one_apply, ← phiC_ev_inv_apply M hM]
      exact ⟨fun h => Equiv.Perm.inv_eq_iff_eq.mpr h.symm,
        fun h => (Equiv.Perm.inv_eq_iff_eq.mp h).symm⟩
    unfold agreeC; rw [hset]
  have hpos : (0 : ℝ) < Fintype.card (Ω M) := by exact_mod_cast Fintype.card_pos
  have h1 : (agreeC (phiC M hM (ev u)) 1 : ℝ) / Fintype.card (Ω M) ≤ (4 * m + 1) / M := by
    rw [hag, div_le_iff₀ hpos]; exact hfix
  have h0 : 0 ≤ (agreeC (phiC M hM (ev u)) 1 : ℝ) / Fintype.card (Ω M) := by positivity
  have : (1 - (1 - (agreeC (phiC M hM (ev u)) 1 : ℝ) / Fintype.card (Ω M))) ^ 2 ≤
      ((4 * m + 1) / (M : ℝ)) ^ 2 := by
    rw [sub_sub_cancel]; exact pow_le_pow_left₀ h0 h1 2
  linarith

/-- The model `f : H₃ → Sym(Fin n)`, `n = |Ω|²`. -/
noncomputable def fUp (hM : 2 ≤ M) (g : H3) : Equiv.Perm (Fin (Fintype.card (Ω M × Ω M))) :=
  (Fintype.equivFin (Ω M × Ω M)).permCongr (PhiP M hM (ev (cwi (cidx g))))

theorem model_ok (hM : 2 ≤ M) (h40 : 40 < M) (r : ℝ) (hdef : 8 / (M : ℝ) ^ 2 ≤ r⁻¹)
    (hexp : ((81 : ℝ) / M) ^ 2 ≤ r⁻¹) : Fintype.card (Ω M × Ω M) ∈ modelSizes E_H r := by
  set e := Fintype.equivFin (Ω M × Ω M)
  refine ⟨Fintype.card_pos, fUp M hM, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · -- `f 1 = 1`
    simp only [fUp, cidx_one]
    have : ev (cwi 0) = 1 := by show ev [] = 1; simp [ev]
    rw [this, map_one]; ext k; simp
  · -- `r⁻¹`-morphism
    intro x hx y hy hxy
    simp only [fUp]
    rw [← Equiv.permCongr_mul, ham_permCongr]
    set P := PhiP M hM (ev (cwi (cidx (x * y))))
    set Q := PhiP M hM (ev (cwi (cidx x))) * PhiP M hM (ev (cwi (cidx y)))
    have e1 : dH P Q = dH (Q * P⁻¹) 1 := by
      rw [← ham_mul_right P Q P⁻¹, mul_inv_cancel, ham_comm]
    have e2 : Q * P⁻¹ = PhiP M hM (ev (cwi (cidx x)) * ev (cwi (cidx y)) *
        (ev (cwi (cidx (x * y))))⁻¹) := by simp only [Q, P, map_mul, map_inv]
    rw [e1, e2]
    have := PhiP_area M hM (chunk_rel_area hx hy hxy)
    calc _ ≤ ((4 : ℕ) : ℝ) * (2 / (M : ℝ) ^ 2) := this
      _ = 8 / (M : ℝ) ^ 2 := by push_cast; ring
      _ ≤ r⁻¹ := hdef
  · -- `(1 - r⁻¹)`-expansive
    intro x hx y hy hne
    simp only [fUp]
    rw [ham_permCongr]
    obtain ⟨hl, hρ⟩ := chunk_sep hx hy hne
    have hsep := PhiP_sep M hM _ 20 hl (by omega) hρ
    have e1 : dH (PhiP M hM (ev (cwi (cidx x)))) (PhiP M hM (ev (cwi (cidx y)))) =
        dH (PhiP M hM (ev (invW (cwi (cidx y)) ++ cwi (cidx x)))) 1 := by
      rw [ev_append, ev_invW, map_mul, map_inv, ← ham_mul_left (PhiP M hM (ev (cwi (cidx y))))⁻¹,
        inv_mul_cancel]
    rw [e1]
    rw [show (4 * ((20 : ℕ) : ℝ) + 1) = 81 by norm_num] at hsep
    linarith

end model

/-! ### The size of the model -/

theorem sqrt_ge (r : ℝ) (hr : 2 ≤ r) : (7 : ℝ) / 5 ≤ √r :=
  Real.le_sqrt_of_sq_le (by nlinarith)

theorem logb_r_ge (r : ℝ) (hr : 2 ≤ r) : 1 ≤ Real.logb 2 r := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hr

/-- **Theorem 1.1, upper bound** (Proposition `prop:sofic-upper` for `E_H`, explicit constant): for
every `r ≥ 2` there is a `(1 - r⁻¹)`-expansive `r⁻¹`-morphism `E_H → Sym_n` with
`n ≤ 2^{7000 √r log₂ r}`. -/
theorem upper_bound (r : ℝ) (hr : 2 ≤ r) :
    ∃ n ∈ modelSizes E_H r, (n : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) := by
  have hs := sqrt_ge r hr
  have hsr : √r ^ 2 = r := Real.sq_sqrt (by linarith)
  set M := ⌈81 * √r⌉₊ with hMdef
  have hM1 : 81 * √r ≤ (M : ℝ) := Nat.le_ceil _
  have hM2 : (M : ℝ) < 81 * √r + 1 := Nat.ceil_lt_add_one (by positivity)
  have hM40 : 40 < M := by
    have : (40 : ℝ) < M := by linarith
    exact_mod_cast this
  have : NeZero M := ⟨by omega⟩
  have hM : 2 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by linarith
  have hMsq : 6561 * r ≤ (M : ℝ) ^ 2 := by nlinarith
  have hrpos : 0 < r := by linarith
  refine ⟨_, model_ok M hM hM40 r ?_ ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hrpos]; nlinarith
  · rw [div_pow, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hrpos]; nlinarith
  · -- size
    have hcard : Fintype.card (Corner.Ω M × Corner.Ω M) = M ^ (12 * M + 18) := by
      rw [Fintype.card_prod, Corner.card_Ω]; unfold Corner.NN; ring
    rw [hcard]
    have hK : ((12 * M + 18 : ℕ) : ℝ) ≤ 1000 * √r := by push_cast; nlinarith
    have hlogr := logb_r_ge r hr
    have hlogM : Real.logb 2 M ≤ 7 * Real.logb 2 r := by
      have h1 : (M : ℝ) ^ 2 ≤ 6724 * r := by nlinarith
      have h2 : Real.logb 2 ((M : ℝ) ^ 2) ≤ Real.logb 2 (6724 * r) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
      rw [Real.logb_pow, Real.logb_mul (by norm_num) (by linarith)] at h2
      have h3 : Real.logb 2 6724 ≤ 13 := by
        rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
        rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      push_cast at h2
      linarith
    have hlogM0 : 0 ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) (by linarith)
    have hpow : ((M ^ (12 * M + 18) : ℕ) : ℝ) = 2 ^ (((12 * M + 18 : ℕ) : ℝ) * Real.logb 2 M) := by
      rw [Nat.cast_pow]
      conv_lhs => rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num) hMpos]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1; ring
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc ((12 * M + 18 : ℕ) : ℝ) * Real.logb 2 M ≤ (1000 * √r) * (7 * Real.logb 2 r) :=
          mul_le_mul hK hlogM hlogM0 (by positivity)
      _ = 7000 * √r * Real.logb 2 r := by ring

/-- **Theorem 1.1, upper bound, profile form**: `σ_{E_H}(r) ≤ 2^{7000 √r log₂ r}` for `r ≥ 2`. -/
theorem profile_upper (r : ℝ) (hr : 2 ≤ r) :
    ∃ n : ℕ, profile E_H r ≤ n ∧ (n : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) := by
  obtain ⟨n, hn, hb⟩ := upper_bound r hr
  exact ⟨n, profile_le_of_mem hn, hb⟩

/-- The statement `SoficUpperStatement` of `Main.lean` holds, with `C = 7000`. -/
theorem soficUpper : SoficUpperStatement := by
  refine ⟨7000, fun r hr => ?_⟩
  obtain ⟨n, hn, hb⟩ := upper_bound r hr
  refine ⟨n, hn, ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
  rw [← Real.sqrt_eq_rpow]
  calc Real.logb 2 n ≤ Real.logb 2 (2 ^ (7000 * √r * Real.logb 2 r)) :=
        Real.logb_le_logb_of_le (by norm_num) hnpos hb
    _ = 7000 * √r * Real.logb 2 r := Real.logb_rpow (by norm_num) (by norm_num)

end Houghton
