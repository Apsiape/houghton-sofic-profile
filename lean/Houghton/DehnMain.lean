import Houghton.DehnCollect
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! Theorem `thm:dehn`, part 4: assembly. The buffered collection reduces a null word `w` of
length `≤ n` to a null word in the `σ_j` (`j ≤ 4n`), whose filling is the Coxeter-insertion
statement `CoxeterFill`. -/

namespace Houghton

lemma wordF_eq_mk : ∀ L : List Letter, wordF L = FreeGroup.mk L
  | [] => rfl
  | x :: L => by
    rw [show (x :: L) = [x] ++ L from rfl, ← FreeGroup.mul_mk, ← wordF_eq_mk L]
    rcases x with ⟨i, _ | _⟩
    · simp [wordF, letterF, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
    · simp [wordF, letterF, FreeGroup.of]

lemma wordF_toWord (w : F) : wordF w.toWord = w := by rw [wordF_eq_mk, FreeGroup.mk_toWord]

lemma rho_of_areaLE {x : F} {n : ℕ} (h : AreaLE x n) : ρH x = 1 := by
  obtain ⟨cs, -, rfl⟩ := h
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rcases c with ⟨z, i, s⟩
    cases s <;> simp [cell, map_mul, map_inv, rho_rel, ih]

lemma rho_eq_of_areaEq {u v : F} {n : ℕ} (h : AreaEq u v n) : ρH u = ρH v := by
  have := rho_of_areaLE h
  rw [map_mul, map_inv, mul_inv_eq_one] at this
  exact this

/-! ### Invariants of the collection fold -/

lemma step_coords (m q : ℕ) (V : SW) (l : Letter) (hm : 1 ≤ m) (hq : 1 ≤ q) :
    ((step (m, q, V) l).1 : ℤ) = m + expA [l] ∧ ((step (m, q, V) l).2.1 : ℤ) = q + expB [l] := by
  rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ <;> simp [step, expA, expB] <;> omega

lemma fold_coords : ∀ (L : List Letter) (m q : ℕ) (V : SW), L.length ≤ m → L.length ≤ q →
    ((L.foldl step (m, q, V)).1 : ℤ) = m + expA L ∧ ((L.foldl step (m, q, V)).2.1 : ℤ) = q + expB L
  | [], m, q, V, _, _ => by simp [expA, expB]
  | l :: L, m, q, V, hm, hq => by
    simp only [List.length_cons] at hm hq
    rw [List.foldl_cons]
    have hcDehn := step_coords m q V l (by omega) (by omega)
    obtain ⟨b1, b2, b3, b4⟩ := step_bounds m q V l
    generalize step (m, q, V) l = st at hcDehn b1 b2 b3 b4
    obtain ⟨m', q', V'⟩ := st
    have ih := fold_coords L m' q' V' (by simp at b1; omega) (by simp at b3; omega)
    have e1 : expA (l :: L) = expA [l] + expA L := by simp [expA]
    have e2 : expB (l :: L) = expB [l] + expB L := by simp [expB]
    simp only at hcDehn
    omega

lemma fold_len (B : ℕ) : ∀ (L : List Letter) (m q : ℕ) (V : SW), q + L.length ≤ B →
    (L.foldl step (m, q, V)).2.2.length ≤ V.length + L.length * (B + 1)
  | [], m, q, V, _ => by simp
  | l :: L, m, q, V, hq => by
    simp only [List.length_cons] at hq
    rw [List.foldl_cons]
    have hl := step_len m q V l
    obtain ⟨b1, b2, b3, b4⟩ := step_bounds m q V l
    generalize step (m, q, V) l = st at hl b1 b2 b3 b4
    obtain ⟨m', q', V'⟩ := st
    have ih := fold_len B L m' q' V' (by simp at b4; omega)
    simp only at hl
    simp only [List.length_cons, Nat.succ_mul]
    omega

lemma fold_idx (B : ℕ) : ∀ (L : List Letter) (m q : ℕ) (V : SW), (∀ x ∈ V, x.1 ≤ B) →
    m + q + 2 * L.length ≤ B → ∀ x ∈ (L.foldl step (m, q, V)).2.2, x.1 ≤ B
  | [], m, q, V, hV, _ => by simpa using hV
  | l :: L, m, q, V, hV, hB => by
    simp only [List.length_cons] at hB
    rw [List.foldl_cons]
    have hi := step_idx m q V l B hV (by omega)
    obtain ⟨b1, b2, b3, b4⟩ := step_bounds m q V l
    generalize step (m, q, V) l = st at hi b1 b2 b3 b4
    obtain ⟨m', q', V'⟩ := st
    exact fold_idx B L m' q' V' hi (by simp at b2 b4; omega)

/-! ### Assembly -/

/-- The Coxeter-insertion statement (the last step of the paper's proof, not yet formalized):
a word in `σ_0, …, σ_B` that is trivial in `H₃` has area at most `K` per letter. -/
def CoxeterFill (B K : ℕ) : Prop :=
  ∀ V : SW, (∀ x ∈ V, x.1 ≤ B) → ρH (σw V) = 1 → AreaLE (σw V) (V.length * K)

/-- **Theorem `thm:dehn`, modulo `CoxeterFill`**: a null word of length `≤ n` has area at most
`n (2n + 2n(1+A)(2n)²) + n(2n+1) K`, where `A ≥ A*(2n)` and `K` is the Coxeter cost per letter
for `σ_0, …, σ_{4n}`. -/
theorem dehn_bound_of_coxeter (n : ℕ) (w : F) (hw : w.toWord.length ≤ n) (h1 : ρH w = 1)
    (A K : ℕ) (hA : AstarLE (2 * n) A) (hC : CoxeterFill (4 * n) K) :
    AreaLE w (n * (2 * n + 2 * n * ((1 + A) * (2 * n) ^ 2)) + n * (2 * n + 1) * K) := by
  set L := w.toWord with hLdef
  have hL : wordF L = w := wordF_toWord w
  have hnull := exp_zero_of_null L (by rw [hL]; exact h1)
  have hcol := collect_list hA L n n [] hw hw (by omega)
  have hco := fold_coords L n n [] hw hw
  have hlen := fold_len (2 * n) L n n [] (by omega)
  have hidx := fold_idx (4 * n) L n n [] (by simp) (by omega)
  generalize L.foldl step (n, n, []) = st at hcol hco hlen hidx
  obtain ⟨m', q', V⟩ := st
  simp only at hco hcol hlen hidx
  have hm' : m' = n := by omega
  have hq' : q' = n := by omega
  rw [hm', hq'] at hcol
  set c := L.length * (2 * n + 2 * n * ((1 + A) * (2 * n) ^ 2)) with hcDehn
  -- `s w s⁻¹ = σw V` at the collection cost
  have h2 : AreaEq (sv n n * w * (sv n n)⁻¹) (σw V) c := by
    have := hcol.mul (AreaEq.refl (sv n n)⁻¹)
    refine areaEq_congr this ?_ ?_ (by omega)
    · simp [σw, hL]
    · group
  have hV1 : ρH (σw V) = 1 := by
    rw [← rho_eq_of_areaEq h2]; simp [map_mul, h1]
  have h3 := (AreaLE.of_areaEq h2 (hC V hidx hV1)).conj (sv n n)⁻¹
  refine (h3.of_eq (by group)).mono ?_
  have e1 : c ≤ n * (2 * n + 2 * n * ((1 + A) * (2 * n) ^ 2)) := Nat.mul_le_mul_right _ hw
  have e2 : V.length * K ≤ n * (2 * n + 1) * K := by
    apply Nat.mul_le_mul_right
    have := Nat.mul_le_mul_right (2 * n + 1) hw
    simp at hlen; omega
  omega

end Houghton
