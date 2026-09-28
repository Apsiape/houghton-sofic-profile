import Std.Tactic

/-! Auxiliary r6 costs nine original cells. The finite lists are checked by
verify107.py. Here the kernel checks exact weights and the conditional all-depth
recurrence, not the group-theoretic derivation of the recurrence. -/
namespace Auxiliary107
def weights : List Nat := [25,616,1,133,78]
def matrix : List (List Nat) :=
  [[4,3,8,4,0],[4,72,120,104,96],[0,0,0,0,0],
   [2,16,36,24,12],[2,10,24,8,12]]
def dot (a b : List Nat) := (List.zipWith (fun x y => x*y) a b).sum
theorem lift107 :
    (List.zipWith (fun row w => decide (dot row weights ≤ 107*w)) matrix weights).all id = true := by decide
theorem original_costs :
    (List.zipWith (fun c w => decide (c ≤ w)) [1,1,1,1,9] weights).all id = true := by decide
theorem finite_rule_costs :
    ([[0,0,1,0,0],[1,2,6,2,6],[0,0,3,0,1],[1,2,12,2,10]].map
      (fun row => decide (dot row weights ≤ 2315))).all id = true := by decide
theorem step (a b l m : Nat) (hl : 1 ≤ l)
    (ha : b ≤ 107*a+2315*l) (hm : m ≤ 26*l+1) :
    b+29*m ≤ 107*(a+29*l) := by omega
theorem all_depth (a l : Nat → Nat)
    (ha0 : a 0 = 0) (hl0 : l 0 = 1)
    (hl : ∀ s, 1 ≤ l s)
    (ha : ∀ s, a (s+1) ≤ 107*a s+2315*l s)
    (hm : ∀ s, l (s+1) ≤ 26*l s+1) :
    ∀ s, a s+29*l s ≤ 29*107^s := by
  intro s
  induction s with
  | zero => simp [ha0,hl0]
  | succ s ih =>
    have hs := step (a s) (a (s+1)) (l s) (l (s+1)) (hl s) (ha s) (hm s)
    have hp : 29*107^(s+1) = 107*(29*107^s) := by
      rw [Nat.pow_succ]; omega
    rw [hp]
    omega
#print axioms lift107
#print axioms all_depth
end Auxiliary107
