import Houghton.Group
import FiniteLean.GroupTheory.Sofic.Profile
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Ring

/-!
# The chunk `E_H` and the transfer to permutation models (Section 5, proof of Theorem 1.1)

`E_H ⊆ H₃` consists of `1`, `a^{±1}, b^{±1}, α^{±1}`, all prefixes of the relators `r₁, …, r₅` (as
written in the paper, `relWord`) and of the word `α a α a⁻¹` for `γ` (`γWord`), and the inverses of these
elements.

Given a `(1 - ε)`-expansive `ε`-morphism `f : E_H → Sym_n`, the homomorphism
`φ_f : F →* Sym_n` defined by `φ_f(x) = f(x)` on the generators satisfies
`dH (φ_f r_i) 1 ≤ 17 ε ≤ 23 ε` and `dH (φ_f γ) 1 ≥ 1 - 5 ε` (`transfer_model`); only the separation
of the pair `γ, 1` is used (`transfer_of`).
Since `f` is an approximate homomorphism for Mathlib's product, `φ_f` is the ordinary Lean
homomorphism (no inversion of generators is needed).
-/

namespace Houghton

open Finset

/-- The prefixes `ws.take k`, `0 ≤ k ≤ |ws|`, of a word. -/
def prefixes (ws : List Letter) : List (List Letter) :=
  (List.range (ws.length + 1)).map ws.take

/-- The words whose values (and their inverses) form `E_H`. -/
def chunkWords : List (List Letter) :=
  [[la], [la'], [lb], [lb'], [lα], [lα']] ++
    ((List.ofFn relWord).flatMap prefixes ++ prefixes γWord)

open Classical in
/-- The symmetric chunk `E_H` of `H₃`. -/
noncomputable def E_H : Finset H3 :=
  (chunkWords.map fun w => ρH' (wordF w)).toFinset ∪
    (chunkWords.map fun w => (ρH' (wordF w))⁻¹).toFinset

theorem mem_E_H_of_word {w : List Letter} (hw : w ∈ chunkWords) : ρH' (wordF w) ∈ E_H := by
  classical
  unfold E_H
  apply mem_union_left
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem inv_mem_E_H_of_word {w : List Letter} (hw : w ∈ chunkWords) : (ρH' (wordF w))⁻¹ ∈ E_H := by
  classical
  unfold E_H
  apply mem_union_right
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem take_mem_prefixes (ws : List Letter) (k : ℕ) : ws.take k ∈ prefixes ws := by
  unfold prefixes
  rw [List.mem_map]
  refine ⟨min k ws.length, List.mem_range.mpr (by omega), ?_⟩
  rcases le_total k ws.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_length, List.take_of_length_le h]

theorem letter_mem_E_H (l : Letter) : ρH' (letterF l) ∈ E_H := by
  have : [l] ∈ chunkWords := by
    obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ := l
    all_goals first | omega | simp [chunkWords]
  have h := mem_E_H_of_word this
  simpa [wordF] using h

theorem relWord_prefix_mem_E_H (i : Fin 5) (k : ℕ) : ρH' (wordF ((relWord i).take k)) ∈ E_H := by
  apply mem_E_H_of_word
  simp only [chunkWords, List.mem_append, List.mem_flatMap, List.mem_ofFn]
  exact Or.inr (Or.inl ⟨relWord i, ⟨i, rfl⟩, take_mem_prefixes _ _⟩)

theorem γWord_prefix_mem_E_H (k : ℕ) : ρH' (wordF (γWord.take k)) ∈ E_H := by
  apply mem_E_H_of_word
  simp only [chunkWords, List.mem_append]
  exact Or.inr (Or.inr (take_mem_prefixes _ _))

theorem one_mem_E_H : (1 : H3) ∈ E_H := by
  have := γWord_prefix_mem_E_H 0
  simpa [wordF] using this

/-- `E_H` is a chunk (it contains `1`). -/
theorem isChunk_E_H : IsChunk E_H := one_mem_E_H

/-- `E_H` is symmetric. -/
theorem inv_mem_E_H {x : H3} (hx : x ∈ E_H) : x⁻¹ ∈ E_H := by
  classical
  unfold E_H at hx ⊢
  rcases mem_union.mp hx with h | h
  · apply mem_union_right
    rw [List.mem_toFinset] at h ⊢
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  · apply mem_union_left
    rw [List.mem_toFinset] at h ⊢
    obtain ⟨w, hw, hx⟩ := List.mem_map.mp h
    rw [← hx, inv_inv]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩

/-! ### The chain estimate -/

section chain

variable {G : Type*} [Group G] {n : ℕ}

/-- Telescoping along the prefixes of a word: each letter costs one multiplication defect `ε`
(except the first, merged with `f 1 = 1`) plus the letter's own error `c l`. -/
theorem chain_bound (E : Finset G) (ε : ℝ) (f : G → Equiv.Perm (Fin n))
    (hf : IsEpsMorphism E ε f) (g : Letter → G) (ψ : Letter → Equiv.Perm (Fin n))
    (c : Letter → ℝ) (hc : ∀ l, dH (f (g l)) (ψ l) ≤ c l) (hg : ∀ l, g l ∈ E) :
    ∀ ws : List Letter, (∀ k, ((ws.take k).map g).prod ∈ E) →
      dH (f (ws.map g).prod) (ws.map ψ).prod ≤ (ws.length.pred : ℝ) * ε + (ws.map c).sum := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; simp [hf.1, ham_self]
  | append_singleton ws l ih =>
    intro hpre
    have hpre' : ∀ k, ((ws.take k).map g).prod ∈ E := by
      intro k
      rcases le_total k ws.length with h | h
      · have := hpre k; rwa [List.take_append_of_le_length h] at this
      · have := hpre ws.length
        rwa [List.take_append_of_le_length le_rfl, List.take_length,
          ← List.take_of_length_le h] at this
    have hws : (ws.map g).prod ∈ E := by
      have := hpre' ws.length; rwa [List.take_length] at this
    have hall : (ws.map g).prod * g l ∈ E := by
      have := hpre (ws.length + 1)
      rw [List.take_of_length_le (by simp)] at this
      simpa using this
    have ih' := ih hpre'
    have key : dH (f ((ws.map g).prod * g l)) ((ws.map ψ).prod * ψ l) ≤
        (if ws = [] then 0 else ε) + dH (f (ws.map g).prod) (ws.map ψ).prod + c l := by
      have hmerge : dH (f ((ws.map g).prod * g l)) (f (ws.map g).prod * f (g l)) ≤
          if ws = [] then 0 else ε := by
        split_ifs with h0
        · subst h0; simp [hf.1, ham_self]
        · exact hf.2 _ hws (g l) (hg l) hall
      have h2 := ham_mul_right (f (ws.map g).prod) (ws.map ψ).prod (f (g l))
      have h3 := ham_mul_left (ws.map ψ).prod (f (g l)) (ψ l)
      have t1 := ham_triangle (f ((ws.map g).prod * g l)) (f (ws.map g).prod * f (g l))
        ((ws.map ψ).prod * ψ l)
      have t2 := ham_triangle (f (ws.map g).prod * f (g l)) ((ws.map ψ).prod * f (g l))
        ((ws.map ψ).prod * ψ l)
      linarith [hc l]
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      List.length_append, List.length_cons, List.length_nil]
    refine key.trans ?_
    rcases eq_or_ne ws [] with h0 | h0
    · subst h0; simp [hf.1, ham_self]
    · simp only [h0, ↓reduceIte]
      have hlen : (ws.length.pred : ℝ) + 1 = ws.length := by
        have : ws.length ≠ 0 := by simpa using h0
        have : ws.length.pred + 1 = ws.length := Nat.succ_pred_eq_of_ne_zero this
        exact_mod_cast this
      have hmul : (ws.length : ℝ) * ε = ws.length.pred * ε + ε := by rw [← hlen]; ring
      simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel, zero_add]
      linarith

end chain

/-! ### The transfer -/

section transfer

variable {n : ℕ}

/-- The homomorphism `F →* Sym_n` defined by `f` on the generators `a, b, α`. -/
def phiOf (f : H3 → Equiv.Perm (Fin n)) : F →* Equiv.Perm (Fin n) :=
  FreeGroup.lift fun i => f (ρH' (FreeGroup.of i))

/-- Cost of a letter: `0` for a generator, `ε` for an inverse generator. -/
def letterCost (ε : ℝ) (l : Letter) : ℝ := if l.2 then 0 else ε

theorem eps_nonneg {E : Finset H3} {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)}
    (hf : IsEpsMorphism E ε f) (h1 : (1 : H3) ∈ E) : 0 ≤ ε := by
  have := hf.2 1 h1 1 h1 (by simpa using h1)
  exact (ham_nonneg _ _).trans this

theorem letter_cost_bound {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (l : Letter) : dH (f (ρH' (letterF l))) (phiOf f (letterF l)) ≤ letterCost ε l := by
  obtain ⟨i, s⟩ := l
  cases s with
  | true => simp [letterF, letterCost, phiOf, ham_self]
  | false =>
    simp only [letterF, letterCost, map_inv, Bool.false_eq_true, ite_false]
    set x := ρH' (FreeGroup.of i)
    have hx : x ∈ E_H := by simpa [letterF] using letter_mem_E_H (i, true)
    have hx' : x⁻¹ ∈ E_H := by simpa [letterF, x] using letter_mem_E_H (i, false)
    have hm := hf.2 x hx x⁻¹ hx' (by simpa using one_mem_E_H)
    rw [mul_inv_cancel, hf.1] at hm
    have : phiOf f (FreeGroup.of i) = f x := by simp [phiOf, x]
    rw [this]
    calc dH (f x⁻¹) (f x)⁻¹ = dH (f x * f x⁻¹) (f x * (f x)⁻¹) := (ham_mul_left _ _ _).symm
      _ = dH 1 (f x * f x⁻¹) := by rw [mul_inv_cancel, ham_comm]
      _ ≤ ε := hm

theorem word_bound {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (ws : List Letter) (hpre : ∀ k, ρH' (wordF (ws.take k)) ∈ E_H) :
    dH (f (ρH' (wordF ws))) (phiOf f (wordF ws)) ≤
      (ws.length.pred : ℝ) * ε + (ws.map (letterCost ε)).sum := by
  have e1 : ∀ v : List Letter, ρH' (wordF v) = (v.map fun l => ρH' (letterF l)).prod := by
    intro v; simp only [wordF, map_list_prod, List.map_map]; rfl
  have e2 : ∀ v : List Letter, phiOf f (wordF v) = (v.map fun l => phiOf f (letterF l)).prod := by
    intro v; simp only [wordF, map_list_prod, List.map_map]; rfl
  have key := chain_bound E_H ε f hf (fun l => ρH' (letterF l)) (fun l => phiOf f (letterF l))
    (letterCost ε) (letter_cost_bound hf) letter_mem_E_H ws (fun k => by rw [← e1]; exact hpre k)
  rw [e1, e2]; exact key

/-- Relator defects: `dH (φ_f r_i) 1 ≤ 17 ε`. -/
theorem rel_bound_17 {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (i : Fin 5) : dH (phiOf f (rel i)) 1 ≤ 17 * ε := by
  have hε := eps_nonneg hf one_mem_E_H
  have h := word_bound hf (relWord i) (relWord_prefix_mem_E_H i)
  rw [wordF_relWord, rho'_rel, hf.1, ham_comm] at h
  refine h.trans ?_
  fin_cases i <;> simp [relWord, letterCost] <;> linarith

/-- Relator defects with the paper's per-relator constant: `dH (φ_f r_i) 1 ≤ (2 l_i - 1) ε`, where
`l_i` is the length of the relator word `r_i`. -/
theorem rel_bound_length {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (i : Fin 5) : dH (phiOf f (rel i)) 1 ≤ (2 * ((relWord i).length : ℝ) - 1) * ε := by
  have hε := eps_nonneg hf one_mem_E_H
  have h := word_bound hf (relWord i) (relWord_prefix_mem_E_H i)
  rw [wordF_relWord, rho'_rel, hf.1, ham_comm] at h
  refine h.trans ?_
  fin_cases i <;> simp [relWord, letterCost] <;> linarith

/-- Relator defects as in the paper: `dH (φ_f r_i) 1 ≤ (2l - 1) ε ≤ 23 ε` (`l ≤ 12`). -/
theorem rel_bound {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (i : Fin 5) : dH (phiOf f (rel i)) 1 ≤ 23 * ε := by
  have hε := eps_nonneg hf one_mem_E_H
  linarith [rel_bound_17 hf i]

/-- `γ ∈ E_H` (the full prefix of `α a α a⁻¹`). -/
theorem rho'_γ_mem_E_H : ρH' γ ∈ E_H := by
  have := γWord_prefix_mem_E_H γWord.length
  rwa [List.take_length, wordF_γWord] at this

/-- Displacement of `γ`, using only the separation of the pair `γ, 1`. -/
theorem gamma_bound_of {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (hsep : 1 - ε ≤ dH (f (ρH' γ)) (f 1)) : 1 - 5 * ε ≤ dH (phiOf f γ) 1 := by
  have h := word_bound hf γWord γWord_prefix_mem_E_H
  rw [wordF_γWord] at h
  have hexp := hsep
  rw [hf.1] at hexp
  have hc : (γWord.length.pred : ℝ) * ε + (γWord.map (letterCost ε)).sum = 4 * ε := by
    simp [γWord, letterCost]; ring
  rw [hc] at h
  have t := ham_triangle (f (ρH' γ)) (phiOf f γ) 1
  linarith

/-- Displacement of `γ`: `dH (φ_f γ) 1 ≥ 1 - 5 ε`. -/
theorem gamma_bound {ε : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H ε f)
    (he : IsExpansive E_H ε f) : 1 - 5 * ε ≤ dH (phiOf f γ) 1 :=
  gamma_bound_of hf (he (ρH' γ) rho'_γ_mem_E_H 1 one_mem_E_H rho'_γ_ne_one)

/-- Transfer from an `r⁻¹`-morphism separating `γ` from `1` (all that Section 5 uses). -/
theorem transfer_of {r : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsEpsMorphism E_H r⁻¹ f)
    (hsep : 1 - r⁻¹ ≤ dH (f (ρH' γ)) (f 1)) :
    (∀ i, dH (phiOf f (rel i)) 1 ≤ 23 / r) ∧ 1 - 5 / r ≤ dH (phiOf f γ) 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · have := rel_bound hf i; rwa [← div_eq_mul_inv] at this
  · have := gamma_bound_of hf hsep; rwa [← div_eq_mul_inv] at this

/-- **Transfer** (Section 5): from a `(1 - r⁻¹)`-expansive `r⁻¹`-morphism `f : E_H → Sym_n`, the
homomorphism `φ_f` has relator defects `≤ 23/r` and moves a fraction `≥ 1 - 5/r` of the points
under `γ`. -/
theorem transfer_model {r : ℝ} {f : H3 → Equiv.Perm (Fin n)} (hf : IsSoficModel E_H r f) :
    (∀ i, dH (phiOf f (rel i)) 1 ≤ 23 / r) ∧ 1 - 5 / r ≤ dH (phiOf f γ) 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · have := rel_bound hf.1 i; rwa [← div_eq_mul_inv] at this
  · have := gamma_bound hf.1 hf.2; rwa [← div_eq_mul_inv] at this

end transfer

end Houghton
