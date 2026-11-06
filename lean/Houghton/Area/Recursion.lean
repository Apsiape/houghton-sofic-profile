import Houghton.Area.Certificates

/-! The doubling recursion (Appendix A, step (3)). Formal words in `t, ρ`: symbols
`0,1,2,3 = t,t⁻¹,ρ,ρ⁻¹`, value `evS`. `X_{2n} = ψ(X_n)`, `X_{2n+1} = b⁻¹X_{2n}bt`;
`W_{2n} = W_n(tρt, R)`, `W_{2n+1} = W_{2n}(tρ, R')t`. `rec_bound`: `Rw(n) + 2|W_n| ≤ 2n^{10}`
(the paper's sharper `Rw(n) ≤ 728/541·864^s` is `Houghton.Area.Sharp`). -/

namespace Houghton

open Word

/-- `X_n = b^{-n} a^n`. -/
def X (n : ℕ) : F := b⁻¹ ^ n * a ^ n

/-! ### Formal words -/

lemma invW_cons (x : ℕ) (w : List ℕ) : invW (x :: w) = invW w ++ [Word.inv x] := by
  simp [invW]

lemma length_invW (w : List ℕ) : (invW w).length = w.length := by simp [invW]

lemma mem_invW {w : List ℕ} {x : ℕ} (h : x ∈ invW w) : ∃ y ∈ w, x = Word.inv y := by
  simp only [invW, List.mem_reverse, List.mem_map] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, hy, rfl⟩

lemma inv_lt4 {x : ℕ} (h : x < 4) : Word.inv x < 4 := by
  rw [inv_eq]; split <;> omega

/-- All symbols are `< 4`. -/
abbrev Syms (w : List ℕ) : Prop := ∀ x ∈ w, x < 4

lemma Syms.invW {w : List ℕ} (h : Syms w) : Syms (invW w) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_invW hx
  exact inv_lt4 (h y hy)

lemma Syms.append {u v : List ℕ} (hu : Syms u) (hv : Syms v) : Syms (u ++ v) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hu x h
  · exact hv x h

lemma Syms.img {u v : List ℕ} (hu : Syms u) (hv : Syms v) (x : ℕ) : Syms (img u v x) := by
  rcases x with _ | _ | _ | x
  · exact hu
  · exact hu.invW
  · exact hv
  · exact hv.invW

lemma Syms.substS {u v : List ℕ} (hu : Syms u) (hv : Syms v) :
    ∀ w : List ℕ, Syms (substS u v w)
  | [] => by intro x hx; simp [Word.substS] at hx
  | x :: w => (Syms.img hu hv x).append (Syms.substS hu hv w)

lemma length_img_le {u v : List ℕ} {L : ℕ} (hu : u.length ≤ L) (hv : v.length ≤ L) (x : ℕ) :
    (img u v x).length ≤ L := by
  rcases x with _ | _ | _ | x <;> simp [img, length_invW, hu, hv]

lemma one_le_length_img {u v : List ℕ} (hu : 1 ≤ u.length) (hv : 1 ≤ v.length) (x : ℕ) :
    1 ≤ (img u v x).length := by
  rcases x with _ | _ | _ | x <;> simp [img, length_invW] <;> omega

lemma length_substS_le {u v : List ℕ} {L : ℕ} (hu : u.length ≤ L) (hv : v.length ≤ L) :
    ∀ w : List ℕ, (substS u v w).length ≤ L * w.length
  | [] => by simp [substS]
  | x :: w => by
    have h1 := length_img_le hu hv x
    have h2 := length_substS_le hu hv w
    simp only [substS, List.length_append, List.length_cons, Nat.mul_succ]
    omega

lemma one_le_length_substS {u v : List ℕ} (hu : 1 ≤ u.length) (hv : 1 ≤ v.length)
    {w : List ℕ} (hw : 1 ≤ w.length) : 1 ≤ (substS u v w).length := by
  rcases w with _ | ⟨x, w⟩
  · simp at hw
  · have := one_le_length_img hu hv x
    simp only [substS, List.length_append]
    omega

lemma substS_append (u v w₁ w₂ : List ℕ) :
    substS u v (w₁ ++ w₂) = substS u v w₁ ++ substS u v w₂ := by
  induction w₁ with
  | nil => simp [substS]
  | cons x w ih => simp [substS, ih]

@[simp] lemma evF_nil (v0 : List ℕ) : evF v0 [] = 1 := rfl

lemma evF_append (v0 w₁ w₂ : List ℕ) : evF v0 (w₁ ++ w₂) = evF v0 w₁ * evF v0 w₂ := by
  simp [evF, substS_append]

lemma evF_cons (v0 : List ℕ) (x : ℕ) (w : List ℕ) :
    evF v0 (x :: w) = evF v0 [x] * evF v0 w := by
  rw [← evF_append]; rfl

lemma evF_0 (v0 : List ℕ) : evF v0 [0] = t := by simp [evF, substS, img, ev_tW]
lemma evF_1 (v0 : List ℕ) : evF v0 [1] = t⁻¹ := by simp [evF, substS, img, ev_invW, ev_tW]
lemma evF_2 (v0 : List ℕ) : evF v0 [2] = ev v0 := by simp [evF, substS, img]
lemma evF_3 (v0 : List ℕ) : evF v0 [3] = (ev v0)⁻¹ := by simp [evF, substS, img, ev_invW]

lemma evF_inv_single (v0 : List ℕ) {x : ℕ} (hx : x < 4) :
    evF v0 [Word.inv x] = (evF v0 [x])⁻¹ := by
  rcases x with _ | _ | _ | _ | x
  · show evF v0 [1] = _; rw [evF_1, evF_0]
  · show evF v0 [0] = _; rw [evF_1, evF_0, inv_inv]
  · show evF v0 [3] = _; rw [evF_3, evF_2]
  · show evF v0 [2] = _; rw [evF_3, evF_2, inv_inv]
  · omega

lemma evF_invW (v0 : List ℕ) {w : List ℕ} (hw : Syms w) : evF v0 (invW w) = (evF v0 w)⁻¹ := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [invW_cons, evF_append, ih (fun y hy => hw y (by simp [hy])),
      evF_inv_single v0 (hw x (by simp)), evF_cons v0 x w, mul_inv_rev]

lemma evS_0 : evS [0] = t := evF_0 rhoW
lemma evS_1 : evS [1] = t⁻¹ := evF_1 rhoW
lemma evS_2 : evS [2] = ρ := (evF_2 rhoW).trans ev_rhoW
lemma evS_3 : evS [3] = ρ⁻¹ := (evF_3 rhoW).trans (by rw [ev_rhoW])
lemma evS_append (w₁ w₂ : List ℕ) : evS (w₁ ++ w₂) = evS w₁ * evS w₂ := evF_append rhoW w₁ w₂
lemma evS_cons (x : ℕ) (w : List ℕ) : evS (x :: w) = evS [x] * evS w := evF_cons rhoW x w

/-- **Substitution lemma**, for any cost relation `Rel` (`AreaEq`, `WAreaEq`): if `f` sends `t` and
the second letter to `u`, `v` up to cost `c` each, it sends `W` to `W(u, v)` up to cost `c |W|`. -/
theorem subst_gen (Rel : F → F → ℕ → Prop) (hone : Rel 1 1 0)
    (hmul : ∀ {u v u' v' : F} {n m : ℕ}, Rel u v n → Rel u' v' m → Rel (u * u') (v * v') (n + m))
    (hinv : ∀ {u v : F} {n : ℕ}, Rel u v n → Rel u⁻¹ v⁻¹ n)
    (f : F →* F) {v0 u v : List ℕ} {c : ℕ} (hu : Syms u) (hv : Syms v)
    (ht : Rel (f t) (evF v0 u) c) (hr : Rel (f (ev v0)) (evF v0 v) c) :
    ∀ W : List ℕ, Syms W → Rel (f (evF v0 W)) (evF v0 (substS u v W)) (c * W.length)
  | [], _ => by simpa [substS] using hone
  | x :: W, hW => by
    have ih := subst_gen Rel hone hmul hinv f hu hv ht hr W (fun y hy => hW y (by simp [hy]))
    have hlet : Rel (f (evF v0 [x])) (evF v0 (img u v x)) c := by
      rcases x with _ | _ | _ | _ | x
      · rw [evF_0]; exact ht
      · rw [evF_1, map_inv, show img u v 1 = invW u from rfl, evF_invW v0 hu]; exact hinv ht
      · rw [evF_2]; exact hr
      · rw [evF_3, map_inv, show img u v 3 = invW v from rfl, evF_invW v0 hv]; exact hinv hr
      · have := hW (x + 1 + 1 + 1 + 1) (by simp); omega
    rw [evF_cons, map_mul]
    show Rel _ (evF v0 (img u v x ++ substS u v W)) _
    rw [evF_append, List.length_cons, Nat.mul_succ, Nat.add_comm]
    exact hmul hlet ih

theorem subst_areaEq (f : F →* F) {u v : List ℕ} {c : ℕ} (hu : Syms u) (hv : Syms v)
    (ht : AreaEq (f t) (evS u) c) (hr : AreaEq (f ρ) (evS v) c) :
    ∀ W : List ℕ, Syms W → AreaEq (f (evS W)) (evS (substS u v W)) (c * W.length) :=
  subst_gen AreaEq (AreaEq.refl 1) AreaEq.mul AreaEq.inv f hu hv ht (by rw [ev_rhoW]; exact hr)

/-! ### The even step: `X_{2n} = ψ(X_n)` -/

lemma ψ_X (m : ℕ) : ψ (X m) = X (2 * m) := by
  simp [X, map_mul, map_pow, map_inv, pow_mul, inv_pow]

lemma psi_t : AreaEq (ψ t) (evS [0, 2, 0]) 0 := by
  apply AreaEq.of_eq
  simp [t, evF, substS, img, tW, rhoW, pow_two, mul_assoc]

lemma psi_ρ : AreaEq (ψ ρ) (evS RS) 84 := area_psi_ρ

lemma syms_RS : Syms RS := by decide
lemma syms_RpS : Syms RpS := by decide

theorem even_step {m r : ℕ} {W : List ℕ} (hW : Syms W) (h : AreaEq (X m) (evS W) r) :
    AreaEq (X (2 * m)) (evS (substS [0, 2, 0] RS W)) (864 * r + 84 * W.length) := by
  have h1 : AreaEq (X (2 * m)) (ψ (evS W)) (864 * r) := by
    have := AreaLE.psi h
    rw [map_mul, map_inv, ψ_X] at this
    exact this
  have h2 := subst_areaEq ψ (by decide) syms_RS (psi_t.mono (by decide)) psi_ρ W hW
  exact h1.trans h2

/-! ### The odd step: `X_{2n+1} = b⁻¹ X_{2n} b t` -/

/-- Conjugation `x ↦ b⁻¹ x b`. -/
def conjB : F →* F := MonoidHom.mk' (fun x => b⁻¹ * x * b) (by intro x y; simp [mul_assoc])

lemma conjB_apply (x : F) : conjB x = b⁻¹ * x * b := rfl

lemma conjB_t : AreaEq (conjB t) (evS [0, 2]) 0 := by
  apply AreaEq.of_eq
  simp [conjB_apply, t, evF, substS, img, tW, rhoW, mul_assoc]

lemma conjB_ρ : AreaEq (conjB ρ) (evS RpS) 14 := by
  rw [conjB_apply]; exact area_N4

lemma X_odd (m : ℕ) : X (2 * m + 1) = conjB (X (2 * m)) * t := by
  rw [X, X, pow_succ' b⁻¹, pow_succ a]
  simp [conjB_apply, t, mul_assoc]

theorem odd_step {m r : ℕ} {W : List ℕ} (hW : Syms W) (h : AreaEq (X (2 * m)) (evS W) r) :
    AreaEq (X (2 * m + 1)) (evS (substS [0, 2] RpS W ++ [0])) (r + 14 * W.length) := by
  have h1 : AreaEq (conjB (X (2 * m))) (conjB (evS W)) r := by
    have := h.conj b⁻¹
    simpa [conjB_apply, AreaEq] using this
  have h2 := subst_areaEq conjB (by decide) syms_RpS (conjB_t.mono (by decide)) conjB_ρ W hW
  have h3 := (h1.trans h2).mul (AreaEq.refl t)
  rw [X_odd, evS_append, evS_0]
  simpa using h3

/-! ### The bound -/

/-- **The doubling recursion**: `X_n = W_n` with `Rw(n) + 2|W_n| ≤ 2 n^{10}`. -/
theorem rec_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ W : List ℕ, ∃ r : ℕ, Syms W ∧ 1 ≤ W.length ∧ AreaEq (X n) (evS W) r ∧
      r + 2 * W.length ≤ 2 * n ^ 10 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- n = 1
    have : n = 1 := by omega
    subst this
    refine ⟨[0], 0, by decide, by simp, ?_, by simp⟩
    rw [evS_0]
    exact AreaEq.of_eq (by simp [X, t])
  · obtain ⟨W, r, hW, hl, hX, hb⟩ := ih (n / 2) (by omega) (by omega)
    set m := n / 2 with hm
    have hP : 1024 * m ^ 10 ≤ n ^ 10 := by
      have : (2 * m) ^ 10 ≤ n ^ 10 := Nat.pow_le_pow_left (by omega) 10
      rw [mul_pow] at this
      simpa using this
    -- even part
    set W' := substS [0, 2, 0] RS W with hW'
    have hX' := even_step hW hX
    have hl'u : W'.length ≤ 46 * W.length :=
      length_substS_le (by decide) (by decide) W
    have hl'l : 1 ≤ W'.length := one_le_length_substS (by decide) (by decide) hl
    have hW'S : Syms W' := Syms.substS (by decide) syms_RS W
    rcases Nat.mod_two_eq_zero_or_one n with hk | hk
    · have hn' : n = 2 * m := by omega
      refine ⟨W', 864 * r + 84 * W.length, hW'S, hl'l, ?_, ?_⟩
      · rw [hn']; exact hX'
      · omega
    · have hn' : n = 2 * m + 1 := by omega
      set W'' := substS [0, 2] RpS W' ++ [0] with hW''
      have hX'' := odd_step hW'S hX'
      have hl''u : W''.length ≤ 7 * W'.length + 1 := by
        have := length_substS_le (u := [0, 2]) (v := RpS) (L := 7) (by decide) (by decide) W'
        simp only [hW'', List.length_append, List.length_singleton]
        omega
      refine ⟨W'', 864 * r + 84 * W.length + 14 * W'.length,
        (Syms.substS (by decide) syms_RpS W').append (by decide), by simp [hW''], ?_, ?_⟩
      · rw [hn']; exact hX''
      · omega

end Houghton
