import Houghton.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Perm.Support

/-!
# Houghton's group `H₃` (Section 2 of Douglas–Mghirbi)

The three rays `Y = {(i,j) : i ∈ {1,2,3}, j ≥ 1}` are encoded as `Fin 3 × ℕ`:
the pair `(i, j) : Fin 3 × ℕ` stands for the paper's point `(i+1, j+1)`.

In the paper permutations act on the **right** and `gh` means "`g` followed by `h`".
Mathlib's `Equiv.Perm` multiplication is composition (`(g * h) y = g (h y)`, right factor first),
so the paper's group is realised inside the opposite group `(Equiv.Perm Y)ᵐᵒᵖ`:
`ρH : F →* (Equiv.Perm Y)ᵐᵒᵖ` sends each letter to `MulOpposite.op` of the paper's permutation, and
`(ρH w).unop` is exactly the paper's evaluation of the word `w`
(`y · (s₁ ⋯ s_l) = (⋯(y · s₁) ⋯) · s_l`, see `rho_word_apply`). `H₃ := ρH.range`.
-/

namespace Houghton

/-- The rays: `(i, j)` encodes the paper's point `(i+1, j+1)`. -/
abbrev Y := Fin 3 × ℕ

/-- The paper's `a`: `(1,1) ↦ (2,1)`, `(1,j) ↦ (1,j-1)` for `j ≥ 2`, `(2,j) ↦ (2,j+1)`, ray 3 fixed. -/
def aFun : Y → Y
  | (⟨0, _⟩, 0) => (1, 0)
  | (⟨0, _⟩, j + 1) => (0, j)
  | (⟨1, _⟩, j) => (1, j + 1)
  | (i, j) => (i, j)

/-- Inverse of `aFun`. -/
def aInv : Y → Y
  | (⟨1, _⟩, 0) => (0, 0)
  | (⟨1, _⟩, j + 1) => (1, j)
  | (⟨0, _⟩, j) => (0, j + 1)
  | (i, j) => (i, j)

/-- The paper's `b`: as `a` with rays 2 and 3 exchanged. -/
def bFun : Y → Y
  | (⟨0, _⟩, 0) => (2, 0)
  | (⟨0, _⟩, j + 1) => (0, j)
  | (⟨2, _⟩, j) => (2, j + 1)
  | (i, j) => (i, j)

/-- Inverse of `bFun`. -/
def bInv : Y → Y
  | (⟨2, _⟩, 0) => (0, 0)
  | (⟨2, _⟩, j + 1) => (2, j)
  | (⟨0, _⟩, j) => (0, j + 1)
  | (i, j) => (i, j)

/-- The paper's `α`: the transposition of `(1,1)` and `(1,2)`. -/
def alFun : Y → Y
  | (⟨0, _⟩, 0) => (0, 1)
  | (⟨0, _⟩, 1) => (0, 0)
  | (i, j) => (i, j)

theorem aInv_aFun : ∀ y, aInv (aFun y) = y := by
  rintro ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ <;> rfl

theorem aFun_aInv : ∀ y, aFun (aInv y) = y := by
  rintro ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ <;> rfl

theorem bInv_bFun : ∀ y, bInv (bFun y) = y := by
  rintro ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ <;> rfl

theorem bFun_bInv : ∀ y, bFun (bInv y) = y := by
  rintro ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ <;> rfl

theorem alFun_alFun : ∀ y, alFun (alFun y) = y := by
  rintro ⟨⟨_ | _ | _ | i, hi⟩, _ | _ | j⟩ <;> rfl

/-- The permutation `a` of `Y`. -/
def aPerm : Equiv.Perm Y := ⟨aFun, aInv, aInv_aFun, aFun_aInv⟩
/-- The permutation `b` of `Y`. -/
def bPerm : Equiv.Perm Y := ⟨bFun, bInv, bInv_bFun, bFun_bInv⟩
/-- The permutation `α` of `Y`. -/
def alPerm : Equiv.Perm Y := ⟨alFun, alFun, alFun_alFun, alFun_alFun⟩

/-- The paper's generators, indexed as in `F` (`0 = a`, `1 = b`, `2 = α`). -/
def genPerm : Fin 3 → Equiv.Perm Y := ![aPerm, bPerm, alPerm]

/-- The paper's evaluation homomorphism `F → H₃ ⊆ Sym(Y)`, with the paper's (right-action)
product realised as the product of `(Equiv.Perm Y)ᵐᵒᵖ`. -/
def ρH : F →* (Equiv.Perm Y)ᵐᵒᵖ := FreeGroup.lift fun i => MulOpposite.op (genPerm i)

/-- Houghton's group `H₃ = ⟨a, b, α⟩`. -/
abbrev H3 : Subgroup (Equiv.Perm Y)ᵐᵒᵖ := ρH.range

/-- The evaluation map onto `H₃`. -/
def ρH' : F →* H3 := ρH.rangeRestrict

/-! ### Words as lists of letters -/

/-- A letter `(i, true) = x_i`, `(i, false) = x_i⁻¹`. -/
abbrev Letter := Fin 3 × Bool

/-- The element of `F` given by a letter. -/
def letterF (l : Letter) : F := if l.2 then FreeGroup.of l.1 else (FreeGroup.of l.1)⁻¹

/-- The element of `F` spelled by a list of letters. -/
def wordF (ws : List Letter) : F := (ws.map letterF).prod

/-- The paper's right action of one letter on a point. -/
def letterAct : Letter → Y → Y
  | (⟨0, _⟩, true) => aFun
  | (⟨0, _⟩, false) => aInv
  | (⟨1, _⟩, true) => bFun
  | (⟨1, _⟩, false) => bInv
  | (_, _) => alFun

/-- The paper's right action of a word: `y · (s₁ ⋯ s_l) = (⋯ (y · s₁) ⋯) · s_l`. -/
def wordAct : List Letter → Y → Y
  | [], y => y
  | l :: ws, y => wordAct ws (letterAct l y)

theorem rho_of (i : Fin 3) : ρH (FreeGroup.of i) = MulOpposite.op (genPerm i) := by
  simp [ρH, FreeGroup.lift_apply_of]

theorem genPerm_apply (i : Fin 3) (y : Y) : genPerm i y = letterAct (i, true) y := by
  fin_cases i <;> rfl

theorem genPerm_inv_apply (i : Fin 3) (y : Y) : (genPerm i)⁻¹ y = letterAct (i, false) y := by
  fin_cases i <;> rfl

theorem rho_letter_apply (l : Letter) (y : Y) : (ρH (letterF l)).unop y = letterAct l y := by
  obtain ⟨i, s⟩ := l
  cases s
  · simp only [letterF, Bool.false_eq_true, ite_false, map_inv, rho_of, MulOpposite.unop_inv,
      MulOpposite.unop_op]
    exact genPerm_inv_apply i y
  · simp only [letterF, ite_true, rho_of, MulOpposite.unop_op]
    exact genPerm_apply i y

/-- `(ρH w).unop` is the paper's right action of the word `w`. -/
theorem rho_word_apply (ws : List Letter) (y : Y) : (ρH (wordF ws)).unop y = wordAct ws y := by
  induction ws generalizing y with
  | nil => simp [wordF, wordAct]
  | cons l ws ih =>
    simp only [wordF, List.map_cons, List.prod_cons, map_mul, MulOpposite.unop_mul,
      Equiv.Perm.mul_apply] at ih ⊢
    rw [rho_letter_apply, ih]
    rfl

theorem rho_eq_one_of (ws : List Letter) (h : ∀ y, wordAct ws y = y) : ρH (wordF ws) = 1 := by
  apply MulOpposite.unop_injective
  refine Equiv.ext fun y => ?_
  rw [rho_word_apply, h]
  rfl

/-! ### The relators as letter lists -/

/-- Letter abbreviations. -/
abbrev la : Letter := (0, true)
abbrev la' : Letter := (0, false)
abbrev lb : Letter := (1, true)
abbrev lb' : Letter := (1, false)
abbrev lα : Letter := (2, true)
abbrev lα' : Letter := (2, false)

/-- The relators `r₁, …, r₅` as the words written in the paper. -/
def relWord : Fin 5 → List Letter := ![
  [lα, lα],
  [lα, la, lα, la', lα, la, lα, la', lα, la, lα, la'],
  [lα, la, la, lα, la', la', lα', la, la, lα', la', la'],
  [la, lb, la', lb', lα'],
  [la, lα, la', lb, lα', lb']]

/-- The word `α a α a⁻¹` for `γ`. -/
def γWord : List Letter := [lα, la, lα, la']

theorem wordF_relWord (i : Fin 5) : wordF (relWord i) = rel i := by
  fin_cases i <;>
    simp [wordF, relWord, letterF, rel, r₁, r₂, r₃, r₄, r₅, comm, a, b, α, pow_succ, mul_assoc]

theorem wordF_γWord : wordF γWord = γ := by
  simp [wordF, γWord, letterF, γ, a, α, mul_assoc]

/-- Each relator acts trivially on every point (checked on the finitely many points where the word
moves anything, and uniformly far out on each ray). -/
theorem wordAct_relWord (i : Fin 5) (y : Y) : wordAct (relWord i) y = y := by
  obtain ⟨⟨_ | _ | _ | i', hi⟩, _ | _ | _ | _ | _ | _ | j⟩ := y <;>
    fin_cases i <;> rfl

/-- The relators `r₁, …, r₅` hold in `H₃`. -/
theorem rho_rel (i : Fin 5) : ρH (rel i) = 1 := by
  rw [← wordF_relWord]; exact rho_eq_one_of _ (wordAct_relWord i)

theorem rho'_rel (i : Fin 5) : ρH' (rel i) = 1 := by
  apply Subtype.ext; exact rho_rel i

/-- `γ` sends `(1,1)` to `(1,3)` (encoded `(0,0) ↦ (0,2)`). -/
theorem wordAct_γWord : wordAct γWord (0, 0) = (0, 2) := rfl

/-- The three-cycle `γ` is nontrivial in `H₃`. -/
theorem rho_γ_ne_one : ρH γ ≠ 1 := by
  intro h
  have := rho_word_apply γWord (0, 0)
  rw [wordF_γWord, h, wordAct_γWord] at this
  exact absurd this (by decide)

theorem rho'_γ_ne_one : ρH' γ ≠ 1 := by
  intro h; apply rho_γ_ne_one
  have := congrArg Subtype.val h
  simpa [ρH'] using this

/-! ### Far commutators (not needed for the lower bound) -/

theorem alPerm_eq_swap : alPerm = Equiv.swap ((0 : Fin 3), 0) ((0 : Fin 3), 1) := by
  ext ⟨⟨_ | _ | _ | i, hi⟩, _ | _ | j⟩ <;> rfl

theorem aPerm_inv_pow_apply (p k : ℕ) : (aPerm⁻¹ ^ p) ((0 : Fin 3), k) = (0, k + p) := by
  induction p generalizing k with
  | zero => rfl
  | succ p ih =>
    rw [pow_succ, Equiv.Perm.mul_apply]
    have : aPerm⁻¹ ((0 : Fin 3), k) = (0, k + 1) := rfl
    rw [this, ih]
    congr 1
    omega

/-- `σ_p` acts as the transposition of the paper's points `(1, p+1)` and `(1, p+2)`. -/
theorem rho_σ_unop (p : ℕ) :
    (ρH (σ p)).unop = Equiv.swap ((0 : Fin 3), p) ((0 : Fin 3), p + 1) := by
  have h1 : (ρH (σ p)).unop = aPerm⁻¹ ^ p * alPerm * (aPerm⁻¹ ^ p)⁻¹ := by
    have ha : ρH a = MulOpposite.op aPerm := rho_of 0
    have hα : ρH α = MulOpposite.op alPerm := rho_of 2
    simp only [σ, map_mul, map_pow, map_inv, ha, hα, MulOpposite.unop_mul, MulOpposite.unop_pow,
      MulOpposite.unop_inv, MulOpposite.unop_op, inv_pow, inv_inv]
    simp only [mul_assoc]
  rw [h1, alPerm_eq_swap, ← Equiv.swap_apply_apply, aPerm_inv_pow_apply, aPerm_inv_pow_apply]
  simp [add_comm]

theorem swap_far_comm (p q : ℕ) (hpq : p + 2 ≤ q ∨ q + 2 ≤ p) :
    Equiv.swap ((0 : Fin 3), p) ((0 : Fin 3), p + 1) * Equiv.swap ((0 : Fin 3), q) (0, q + 1) =
      Equiv.swap ((0 : Fin 3), q) ((0 : Fin 3), q + 1) * Equiv.swap ((0 : Fin 3), p) (0, p + 1) := by
  have h : [((0 : Fin 3), p), ((0 : Fin 3), p + 1), ((0 : Fin 3), q), ((0 : Fin 3), q + 1)].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, true_and,
      List.nodup_nil, or_false, not_or, and_true, not_false_eq_true]
    omega
  exact (Equiv.Perm.disjoint_swap_swap h).commute

/-- The far commutators `[σ_p^{±1}, σ_q^{±1}]`, `|p - q| ≥ 2`, are trivial in `H₃`. -/
theorem rho_far_comm (p q : ℕ) (hpq : p + 2 ≤ q ∨ q + 2 ≤ p) (e₁ e₂ : Bool) :
    ρH (comm (if e₁ then σ p else (σ p)⁻¹) (if e₂ then σ q else (σ q)⁻¹)) = 1 := by
  have hx : ∀ (e : Bool) (m : ℕ), (ρH (if e then σ m else (σ m)⁻¹)).unop =
      Equiv.swap ((0 : Fin 3), m) ((0 : Fin 3), m + 1) := by
    intro e m
    cases e <;> simp [rho_σ_unop, Equiv.swap_inv]
  apply MulOpposite.unop_injective
  simp only [comm, map_mul, map_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, hx,
    Equiv.swap_inv, MulOpposite.unop_one]
  have hc := swap_far_comm p q hpq
  calc _ = Equiv.swap ((0 : Fin 3), q) ((0 : Fin 3), q + 1) *
        (Equiv.swap ((0 : Fin 3), p) (0, p + 1) * Equiv.swap ((0 : Fin 3), q) (0, q + 1)) *
          Equiv.swap ((0 : Fin 3), p) (0, p + 1) := by simp only [mul_assoc]
    _ = 1 := by
      rw [hc]
      simp only [← mul_assoc, Equiv.swap_mul_self, one_mul]

end Houghton
