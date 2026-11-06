import Houghton.Basic
import Houghton.Area.Word

/-! Soundness of the checker: `checkPacked_sound : checkPacked data target = true →
AreaLE (ev target) data.length`, where `ev` evaluates a letter word in `F`. -/

namespace Houghton

open Word

/-- The generator with index `k mod 3`. -/
def genN (k : ℕ) : F := FreeGroup.of ⟨k % 3, Nat.mod_lt _ (by decide)⟩

/-- The value of a letter. -/
def ltr (n : ℕ) : F := if n % 2 = 0 then genN (n / 2) else (genN (n / 2))⁻¹

/-- The value of a word. -/
def ev (w : List ℕ) : F := (w.map ltr).prod

@[simp] lemma ev_nil : ev [] = 1 := rfl

@[simp] lemma ev_cons (x : ℕ) (w : List ℕ) : ev (x :: w) = ltr x * ev w := by
  simp [ev]

@[simp] lemma ev_append (u v : List ℕ) : ev (u ++ v) = ev u * ev v := by
  simp [ev, List.prod_append]

lemma ev_singleton (x : ℕ) : ev [x] = ltr x := by simp

@[simp] lemma ltr_0 : ltr 0 = a := rfl
@[simp] lemma ltr_1 : ltr 1 = a⁻¹ := rfl
@[simp] lemma ltr_2 : ltr 2 = b := rfl
@[simp] lemma ltr_3 : ltr 3 = b⁻¹ := rfl
@[simp] lemma ltr_4 : ltr 4 = α := rfl
@[simp] lemma ltr_5 : ltr 5 = α⁻¹ := rfl

lemma inv_eq (x : ℕ) : Word.inv x = if x % 2 = 0 then x + 1 else x - 1 := by
  unfold Word.inv
  cases h : Nat.beq (x % 2) 0
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

lemma ltr_inv (x : ℕ) : ltr (Word.inv x) = (ltr x)⁻¹ := by
  rw [inv_eq]
  by_cases h : x % 2 = 0
  · have h1 : ¬ (x + 1) % 2 = 0 := by omega
    have h2 : (x + 1) / 2 = x / 2 := by omega
    simp [ltr, h, h1, h2]
  · have h1 : (x - 1) % 2 = 0 := by omega
    have h2 : (x - 1) / 2 = x / 2 := by omega
    simp [ltr, h, h1, h2]

lemma ev_invW (w : List ℕ) : ev (invW w) = (ev w)⁻¹ := by
  induction w with
  | nil => simp [invW]
  | cons x w ih =>
    have : invW (x :: w) = invW w ++ [Word.inv x] := by simp [invW]
    rw [this, ev_append, ih, ev_singleton, ltr_inv, ev_cons, mul_inv_rev]

/-! ### The stack semantics -/

lemma ev_push (stk : List ℕ) (x : ℕ) :
    ev (push stk x).reverse = ev stk.reverse * ltr x := by
  cases stk with
  | nil => simp [push]
  | cons y s =>
    simp only [push]
    cases h : Nat.beq y (Word.inv x)
    · simp [mul_assoc]
    · have := Nat.eq_of_beq_eq_true h
      subst this
      simp [ltr_inv, mul_assoc]

lemma pushW_cons (stk : List ℕ) (x : ℕ) (w : List ℕ) :
    pushW stk (x :: w) = pushW (push stk x) w := by
  rw [pushW]
  split <;> simp_all

lemma ev_pushW (stk w : List ℕ) : ev (pushW stk w).reverse = ev stk.reverse * ev w := by
  induction w generalizing stk with
  | nil => simp [pushW]
  | cons x w ih => rw [pushW_cons, ih, ev_push, ev_cons, mul_assoc]

/-- The relator index as an element of `Fin 5`. -/
def idx (i : ℕ) : Fin 5 := ⟨min i 4, by omega⟩

lemma ev_relW (i : ℕ) : ev (relW i) = rel (idx i) := by
  rcases i with _ | _ | _ | _ | i
  · simp [relW, idx, rel, r₁, pow_two]
  · simp [relW, idx, rel, r₂, pow_succ, mul_assoc]
  · simp [relW, idx, rel, r₃, comm, pow_two, mul_assoc]
  · simp [relW, idx, rel, r₄, mul_assoc]
  · have h1 : relW (i + 1 + 1 + 1 + 1) = [0, 4, 1, 2, 5, 3] := rfl
    have h2 : idx (i + 1 + 1 + 1 + 1) = 4 := by ext; simp [idx]
    rw [h1, h2]
    simp [rel, r₅, mul_assoc]

/-- The cell `z · val(i)^{±1} · z⁻¹` for an arbitrary valuation `val` of the relator indices. -/
def gcell (val : ℕ → F) (c : F × ℕ × Bool) : F :=
  c.1 * (if c.2.2 then val c.2.1 else (val c.2.1)⁻¹) * c.1⁻¹

/-- The cell of `F` described by a word cell. -/
def toGCell (c : Word.Cell) : F × ℕ × Bool := (ev c.1, c.2.1, c.2.2)

section Generic

variable (R : ℕ → List ℕ) (val : ℕ → F) (hR : ∀ i, ev (R i) = val i)
include hR

lemma ev_runCell (stk : List ℕ) (c : Word.Cell) :
    ev (runCell R stk c).reverse = ev stk.reverse * gcell val (toGCell c) := by
  cases h : c.2.2 <;>
    simp [runCell, pushRel, h, ev_pushW, ev_invW, hR, gcell, toGCell, mul_assoc]

lemma ev_run (stk : List ℕ) (cs : List Word.Cell) :
    ev (run R stk cs).reverse = ev stk.reverse * ((cs.map toGCell).map (gcell val)).prod := by
  induction cs generalizing stk with
  | nil => simp [run]
  | cons c cs ih =>
    have : run R stk (c :: cs) = run R (runCell R stk c) cs := by rw [run]; split <;> simp_all
    rw [this, ih, ev_runCell R val hR]; simp [mul_assoc]

end Generic

lemma beqL_eq : ∀ u v : List ℕ, beqL u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [beqL] at h
  | _ :: _, [], h => by simp [beqL] at h
  | x :: xs, y :: ys, h => by
    simp only [beqL] at h
    cases hxy : Nat.beq x y
    · rw [hxy] at h; simp at h
    · rw [hxy] at h
      rw [Nat.eq_of_beq_eq_true hxy, beqL_eq xs ys h]

/-- **Generic soundness of the checker**: the cells multiply to the target in `F`. -/
theorem checkPacked_prod (R : ℕ → List ℕ) (val : ℕ → F) (hR : ∀ i, ev (R i) = val i)
    (data target : List ℕ) (h : checkPacked R data target = true) :
    (((data.map decodeCell).map toGCell).map (gcell val)).prod = ev target := by
  have h1 := ev_run R val hR [] (data.map decodeCell)
  rw [beqL_eq _ _ h, ev_pushW] at h1
  simpa using h1.symm

/-- **Soundness of the checker** for Johnson's presentation. -/
theorem checkPacked_sound (data : List ℕ) (target : List ℕ)
    (h : checkPacked relW data target = true) : AreaLE (ev target) data.length := by
  refine ⟨((data.map decodeCell).map toGCell).map fun c => (c.1, idx c.2.1, c.2.2), by simp, ?_⟩
  rw [← checkPacked_prod relW (fun i => rel (idx i)) ev_relW data target h, List.map_map]
  rfl

end Houghton
