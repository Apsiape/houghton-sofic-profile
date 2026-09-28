import Std.Tactic

/-!
This file checks the integer-scaled arithmetic in
Paper A's reweighted-area argument, not the geometric/group-theoretic premises.
No `sorry`, new axioms, or native_decide are used.
-/

namespace CausalReleaseAudit

def C : List (List Nat) :=
  [[4, 0, 1, 8, 4], [108, 32, 31, 128, 60],
   [204, 68, 64, 384, 144], [0, 0, 0, 0, 0], [36, 12, 14, 84, 36]]

-- Ten times the manuscript's rational weight vector.
def w10 : List Nat := [10, 315, 676, 0, 145]

def dot (xs ys : List Nat) : Nat :=
  (List.zipWith (fun x y => x * y) xs ys).sum

theorem substitution_row_sums : C.map List.sum = [17, 359, 864, 0, 182] := by
  decide

theorem weighted_lift_multiplier :
    (List.zipWith (fun row w => decide (dot row w10 ≤ 130 * w)) C w10).all id = true := by
  decide

theorem ordinary_area_from_weight :
    (List.zipWith (fun row w => decide (10 * row.sum ≤ 17 * w)) C w10).all id = true := by
  decide

theorem cheap_word_even_weights :
    dot [1, 18] [2, 1] ≤ 96 ∧ dot [1, 18] [26, 20] ≤ 96 * 18 := by
  decide

theorem cheap_word_odd_weights : 96 ≤ 96 ∧ 1654 ≤ 96 * 18 := by
  decide

theorem weighted_inhomogeneous_bound (T R : Nat) :
    3 * (48 * T + 1248 * R) ≤ 208 * (T + 18 * R) := by
  omega

theorem ordinary_inhomogeneous_bound (T R : Nat) :
    9 * (14 * T + 364 * R) ≤ 182 * (T + 18 * R) := by
  omega

-- Clear positive denominators in
-- 17*(21/10) + (182/9)*(96/95) < (9/20)*130.
theorem ordinary_last_lift_constant :
    17 * 21 * 9 * 95 * 20 + 182 * 96 * 10 * 20 <
      9 * 130 * 10 * 9 * 95 := by
  decide

theorem final_constant_below_thirty : 2841 < 30 * 95 := by
  decide

-- Conditional all-depth induction: L is an upper envelope for cheap-word
-- weights, W is ten times a weighted area. The recurrence hypotheses are
-- mathematical premises; this theorem does not certify their provenance.
theorem depth_recurrences
    (L W : Nat → Nat)
    (hL0 : L 0 ≤ 1) (hW0 : W 0 = 0)
    (hL : ∀ s, L (s + 1) ≤ 96 * L s + 1)
    (hW : ∀ s, 3 * W (s + 1) ≤ 390 * W s + 2080 * L s) :
    ∀ s, (95 * L s + 1 ≤ 96 ^ (s + 1)) ∧
      (1615 * W s + 33280 * 96 ^ s ≤ 33280 * 130 ^ s) := by
  intro s
  induction s with
  | zero =>
      simp only [Nat.zero_add, Nat.pow_zero, Nat.pow_one]
      omega
  | succ s ih =>
      obtain ⟨ihL, ihW⟩ := ih
      have nextL := hL s
      have nextW := hW s
      have p96 : 96 ^ (s + 1) = 96 * 96 ^ s := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have p130 : 130 ^ (s + 1) = 130 * 130 ^ s := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have pp96 : 96 ^ (s + 1 + 1) = 96 * (96 * 96 ^ s) := by
        rw [Nat.pow_succ, p96, Nat.mul_comm]
      rw [pp96, p96, p130]
      rw [p96] at ihL
      constructor <;> omega

-- Conditional insertion-cost arithmetic; no Coxeter-word semantics are claimed.
def insertionCharge : Nat → Nat
  | 0 => 0
  | d + 1 => insertionCharge d + d + 2

theorem insertion_charge_formula (d : Nat) :
    2 * insertionCharge d = d * (d + 3) := by
  induction d with
  | zero => decide
  | succ d ih =>
      simp only [insertionCharge, Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] at ih ⊢
      omega

#print axioms insertion_charge_formula
#print axioms substitution_row_sums
#print axioms weighted_lift_multiplier
#print axioms ordinary_area_from_weight
#print axioms depth_recurrences

end CausalReleaseAudit
