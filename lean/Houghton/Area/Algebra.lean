import Houghton.Basic

/-! The algebra of `AreaLE` and of `AreaEq u v n := AreaLE (u * v⁻¹) n`. -/

namespace Houghton

lemma AreaLE.mono {w : F} {n m : ℕ} (h : AreaLE w n) (hnm : n ≤ m) : AreaLE w m := by
  obtain ⟨cs, hl, hp⟩ := h
  exact ⟨cs, hl.trans hnm, hp⟩

lemma AreaLE.one : AreaLE 1 0 := ⟨[], le_rfl, by simp⟩

lemma AreaLE.of_eq {w w' : F} {n : ℕ} (h : AreaLE w n) (e : w = w') : AreaLE w' n := e ▸ h

lemma AreaLE.of_eq_one {w : F} (e : w = 1) : AreaLE w 0 := AreaLE.one.of_eq e.symm

lemma AreaLE.mul {u v : F} {n m : ℕ} (hu : AreaLE u n) (hv : AreaLE v m) :
    AreaLE (u * v) (n + m) := by
  obtain ⟨cs, hl, hp⟩ := hu
  obtain ⟨ds, hl', hp'⟩ := hv
  exact ⟨cs ++ ds, by simp; omega, by simp [List.prod_append, hp, hp']⟩

/-- Conjugating a cell. -/
def conjCell (g : F) (c : F × Fin 5 × Bool) : F × Fin 5 × Bool := (g * c.1, c.2)

lemma cell_conjCell (g : F) (c : F × Fin 5 × Bool) : cell (conjCell g c) = g * cell c * g⁻¹ := by
  rcases c with ⟨z, i, s⟩
  cases s <;> simp [cell, conjCell, mul_assoc, mul_inv_rev]

lemma prod_map_conj (g : F) (L : List F) :
    (L.map fun x => g * x * g⁻¹).prod = g * L.prod * g⁻¹ := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    simp [mul_assoc]

lemma AreaLE.conj {w : F} {n : ℕ} (g : F) (h : AreaLE w n) : AreaLE (g * w * g⁻¹) n := by
  obtain ⟨cs, hl, hp⟩ := h
  refine ⟨cs.map (conjCell g), by simpa using hl, ?_⟩
  have : (cs.map (conjCell g)).map cell = (cs.map cell).map (fun x => g * x * g⁻¹) := by
    simp [List.map_map, Function.comp_def, cell_conjCell]
  rw [this, prod_map_conj, hp]

/-- Inverting a cell. -/
def invCell (c : F × Fin 5 × Bool) : F × Fin 5 × Bool := (c.1, c.2.1, !c.2.2)

lemma cell_invCell (c : F × Fin 5 × Bool) : cell (invCell c) = (cell c)⁻¹ := by
  rcases c with ⟨z, i, s⟩
  cases s <;> simp [cell, invCell, mul_assoc]

lemma prod_inv_reverse' (L : List F) : L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih, List.prod_append, mul_inv_rev]

lemma AreaLE.inv {w : F} {n : ℕ} (h : AreaLE w n) : AreaLE w⁻¹ n := by
  obtain ⟨cs, hl, hp⟩ := h
  refine ⟨(cs.map invCell).reverse, by simpa using hl, ?_⟩
  rw [← hp, prod_inv_reverse']
  simp [List.map_reverse, Function.comp_def, cell_invCell]

lemma AreaLE.cell (c : F × Fin 5 × Bool) : AreaLE (cell c) 1 := ⟨[c], by simp, by simp⟩

lemma AreaLE.rel (i : Fin 5) : AreaLE (rel i) 1 :=
  (AreaLE.cell (1, i, true)).of_eq (by simp [Houghton.cell])

/-! ### Rewriting with cost -/

/-- `u` equals `v` modulo at most `n` cells. -/
def AreaEq (u v : F) (n : ℕ) : Prop := AreaLE (u * v⁻¹) n

lemma AreaEq.mono {u v : F} {n m : ℕ} (h : AreaEq u v n) (hnm : n ≤ m) : AreaEq u v m :=
  AreaLE.mono h hnm

lemma AreaEq.of_eq {u v : F} (h : u = v) : AreaEq u v 0 :=
  AreaLE.of_eq_one (by simp [h])

lemma AreaEq.refl (u : F) : AreaEq u u 0 := AreaEq.of_eq rfl

lemma AreaEq.symm {u v : F} {n : ℕ} (h : AreaEq u v n) : AreaEq v u n :=
  (AreaLE.inv h).of_eq (by simp [mul_inv_rev])

lemma AreaEq.trans {u v w : F} {n m : ℕ} (h₁ : AreaEq u v n) (h₂ : AreaEq v w m) :
    AreaEq u w (n + m) :=
  (AreaLE.mul h₁ h₂).of_eq (by simp [mul_assoc])

lemma AreaEq.mul {u v u' v' : F} {n m : ℕ} (h₁ : AreaEq u v n) (h₂ : AreaEq u' v' m) :
    AreaEq (u * u') (v * v') (n + m) := by
  have := AreaLE.mul (AreaLE.conj u h₂) h₁
  rw [Nat.add_comm]
  exact this.of_eq (by simp [mul_assoc, mul_inv_rev])

lemma AreaEq.inv {u v : F} {n : ℕ} (h : AreaEq u v n) : AreaEq u⁻¹ v⁻¹ n :=
  (AreaLE.conj u⁻¹ (AreaLE.inv h)).of_eq (by simp [mul_assoc, mul_inv_rev])

lemma AreaEq.conj {u v : F} {n : ℕ} (g : F) (h : AreaEq u v n) :
    AreaEq (g * u * g⁻¹) (g * v * g⁻¹) n :=
  (AreaLE.conj g h).of_eq (by simp [mul_assoc, mul_inv_rev])

lemma AreaLE.of_areaEq {u v : F} {n m : ℕ} (h : AreaEq u v n) (hv : AreaLE v m) :
    AreaLE u (n + m) :=
  (AreaLE.mul h hv).of_eq (by simp)

/-! ### Commutators -/

lemma comm_mul_right_eq (x y z : F) : comm x (y * z) = comm x y * (y * comm x z * y⁻¹) := by
  simp [comm, mul_assoc, mul_inv_rev]

lemma comm_inv_right_eq (x y : F) : comm x y⁻¹ = y⁻¹ * (comm x y)⁻¹ * y⁻¹⁻¹ := by
  simp [comm, mul_assoc, mul_inv_rev]

lemma comm_swap_eq (x y : F) : comm y x = (comm x y)⁻¹ := by
  simp [comm, mul_assoc, mul_inv_rev]

lemma comm_inv_left_eq (x y : F) : comm x⁻¹ y = x⁻¹ * comm y x * x⁻¹⁻¹ := by
  simp [comm, mul_assoc]

lemma AreaLE.comm_symm {x y : F} {n : ℕ} (h : AreaLE (comm x y) n) : AreaLE (comm y x) n := by
  rw [comm_swap_eq]; exact h.inv

lemma AreaLE.comm_inv_right {x y : F} {n : ℕ} (h : AreaLE (comm x y) n) :
    AreaLE (comm x y⁻¹) n := by
  rw [comm_inv_right_eq]; exact h.inv.conj _

lemma AreaLE.comm_inv_left {x y : F} {n : ℕ} (h : AreaLE (comm x y) n) :
    AreaLE (comm x⁻¹ y) n := by
  rw [comm_inv_left_eq]; exact h.comm_symm.conj _

lemma AreaLE.comm_mul_right {x y z : F} {n m : ℕ} (h₁ : AreaLE (comm x y) n)
    (h₂ : AreaLE (comm x z) m) : AreaLE (comm x (y * z)) (n + m) := by
  rw [comm_mul_right_eq]; exact h₁.mul (h₂.conj y)

lemma AreaLE.comm_pow_right {x y : F} {n : ℕ} (h : AreaLE (comm x y) n) (k : ℕ) :
    AreaLE (comm x (y ^ k)) (k * n) := by
  induction k with
  | zero =>
    simp only [pow_zero, Nat.zero_mul]
    exact AreaLE.of_eq_one (by simp [comm])
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.comm_mul_right h

lemma AreaEq.comm {x x' y y' : F} {n m : ℕ} (h₁ : AreaEq x x' n) (h₂ : AreaEq y y' m) :
    AreaEq (comm x y) (comm x' y') (n + m + n + m) := by
  unfold Houghton.comm
  exact ((h₁.mul h₂).mul h₁.inv).mul h₂.inv

end Houghton
