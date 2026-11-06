import Houghton.Group

/-! Theorem `thm:dehn`, part 2: the quotient coordinates. A null word has zero exponent sum in `a`
and in `b` (read off from the eventual translations on rays 2 and 3; no presentation is used). -/

namespace Houghton

/-- Exponent sum of `a`. -/
def expA : List Letter → ℤ
  | [] => 0
  | l :: L => (if l = (0, true) then 1 else if l = (0, false) then -1 else 0) + expA L

/-- Exponent sum of `b`. -/
def expB : List Letter → ℤ
  | [] => 0
  | l :: L => (if l = (1, true) then 1 else if l = (1, false) then -1 else 0) + expB L

lemma wordAct_ray2 : ∀ (L : List Letter) (j : ℕ), L.length ≤ j →
    ((wordAct L ((1 : Fin 3), j)).1 = 1 ∧ ((wordAct L ((1 : Fin 3), j)).2 : ℤ) = j + expA L)
  | [], j, _ => by simp [wordAct, expA]
  | l :: L, j, hj => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
    have hL : L.length ≤ j := by simp at hj; omega
    rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩
    · obtain ⟨h1, h2⟩ := wordAct_ray2 L j (by omega)
      change (wordAct L ((1 : Fin 3), j)).1 = 1 ∧ ((wordAct L ((1 : Fin 3), j)).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expA]
    · obtain ⟨h1, h2⟩ := wordAct_ray2 L (j + 2) (by omega)
      change (wordAct L ((1 : Fin 3), (j + 2))).1 = 1 ∧ ((wordAct L ((1 : Fin 3), (j + 2))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expA]; omega
    · obtain ⟨h1, h2⟩ := wordAct_ray2 L (j + 1) (by omega)
      change (wordAct L ((1 : Fin 3), (j + 1))).1 = 1 ∧ ((wordAct L ((1 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expA]
    · obtain ⟨h1, h2⟩ := wordAct_ray2 L (j + 1) (by omega)
      change (wordAct L ((1 : Fin 3), (j + 1))).1 = 1 ∧ ((wordAct L ((1 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expA]
    · obtain ⟨h1, h2⟩ := wordAct_ray2 L (j + 1) (by omega)
      change (wordAct L ((1 : Fin 3), (j + 1))).1 = 1 ∧ ((wordAct L ((1 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expA]
    · obtain ⟨h1, h2⟩ := wordAct_ray2 L (j + 1) (by omega)
      change (wordAct L ((1 : Fin 3), (j + 1))).1 = 1 ∧ ((wordAct L ((1 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expA]
    · omega
    · omega

lemma wordAct_ray3 : ∀ (L : List Letter) (j : ℕ), L.length ≤ j →
    ((wordAct L ((2 : Fin 3), j)).1 = 2 ∧ ((wordAct L ((2 : Fin 3), j)).2 : ℤ) = j + expB L)
  | [], j, _ => by simp [wordAct, expB]
  | l :: L, j, hj => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
    have hL : L.length ≤ j := by simp at hj; omega
    rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩
    · obtain ⟨h1, h2⟩ := wordAct_ray3 L (j + 1) (by omega)
      change (wordAct L ((2 : Fin 3), (j + 1))).1 = 2 ∧ ((wordAct L ((2 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expB]
    · obtain ⟨h1, h2⟩ := wordAct_ray3 L (j + 1) (by omega)
      change (wordAct L ((2 : Fin 3), (j + 1))).1 = 2 ∧ ((wordAct L ((2 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expB]
    · obtain ⟨h1, h2⟩ := wordAct_ray3 L j (by omega)
      change (wordAct L ((2 : Fin 3), j)).1 = 2 ∧ ((wordAct L ((2 : Fin 3), j)).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expB]
    · obtain ⟨h1, h2⟩ := wordAct_ray3 L (j + 2) (by omega)
      change (wordAct L ((2 : Fin 3), (j + 2))).1 = 2 ∧ ((wordAct L ((2 : Fin 3), (j + 2))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expB]; omega
    · obtain ⟨h1, h2⟩ := wordAct_ray3 L (j + 1) (by omega)
      change (wordAct L ((2 : Fin 3), (j + 1))).1 = 2 ∧ ((wordAct L ((2 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expB]
    · obtain ⟨h1, h2⟩ := wordAct_ray3 L (j + 1) (by omega)
      change (wordAct L ((2 : Fin 3), (j + 1))).1 = 2 ∧ ((wordAct L ((2 : Fin 3), (j + 1))).2 : ℤ) = _
      refine ⟨h1, ?_⟩
      rw [h2]; simp [expB]
    · omega
    · omega

/-- **Quotient coordinates of a null word**: zero exponent sums in `a` and in `b`. -/
theorem exp_zero_of_null (L : List Letter) (h : ρH (wordF L) = 1) : expA L = 0 ∧ expB L = 0 := by
  have h2 := wordAct_ray2 L L.length le_rfl
  have h3 := wordAct_ray3 L L.length le_rfl
  have e2 := rho_word_apply L ((1 : Fin 3), L.length)
  have e3 := rho_word_apply L ((2 : Fin 3), L.length)
  rw [h] at e2 e3
  simp only [MulOpposite.unop_one, Equiv.Perm.coe_one, id] at e2 e3
  rw [← e2] at h2
  rw [← e3] at h3
  simp at h2 h3
  omega

end Houghton
