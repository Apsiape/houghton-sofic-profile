import FiniteLean.GroupTheory.Permutations.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Finite.Prod

/-!
# Chunks, ε-morphisms and Cornulier's sofic profile (Section 2)

`dH` (from `Houghton.Basic`) is the normalized Hamming distance.

**Convention.** Mathlib multiplies permutations by composition (`(g * h) x = g (h x)`, the right
factor acts first); the paper multiplies them "left factor first". We use Mathlib's product in the
definition of an `ε`-morphism (`IsEpsMorphism`). This does not change the profile: inversion
`g ↦ g⁻¹` is an anti-isomorphism of `Sym_n` preserving `dH`, so `f ↦ (f ·)⁻¹` is a bijection between
models in the two conventions (`modelSizesPaper_eq` proves the sets of admissible `n` coincide).

A map `E → Sym_n` is represented by a function `f : G → Equiv.Perm (Fin n)`; its values off `E`
are irrelevant to every definition below.
-/

namespace Houghton

open Finset

section dH

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem ham_nonneg (g h : Equiv.Perm Ω) : 0 ≤ dH g h :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ham_self (g : Equiv.Perm Ω) : dH g g = 0 := by
  simp [dH]

theorem ham_comm (g h : Equiv.Perm Ω) : dH g h = dH h g := by
  simp only [dH, ne_comm]

theorem ham_triangle (g h k : Equiv.Perm Ω) : dH g k ≤ dH g h + dH h k := by
  unfold dH
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsub : (univ.filter fun x => g x ≠ k x) ⊆
      (univ.filter fun x => g x ≠ h x) ∪ (univ.filter fun x => h x ≠ k x) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    by_contra hc
    push Not at hc
    exact hx (hc.1.trans hc.2)
  exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)

theorem ham_mul_left (k g h : Equiv.Perm Ω) : dH (k * g) (k * h) = dH g h := by
  simp [dH, Equiv.Perm.mul_apply]

theorem ham_mul_right (g h k : Equiv.Perm Ω) : dH (g * k) (h * k) = dH g h := by
  have hc : (univ.filter fun x => (g * k) x ≠ (h * k) x).card =
      (univ.filter fun x => g x ≠ h x).card := by
    apply card_equiv k
    intro x
    simp only [mem_filter, mem_univ, true_and]
    rfl
  unfold dH
  rw [hc]

theorem ham_inv (g h : Equiv.Perm Ω) : dH g⁻¹ h⁻¹ = dH g h := by
  calc dH g⁻¹ h⁻¹ = dH (g⁻¹ * g) (h⁻¹ * g) := (ham_mul_right _ _ _).symm
    _ = dH (h * (g⁻¹ * g)) (h * (h⁻¹ * g)) := (ham_mul_left _ _ _).symm
    _ = dH g h := by simp [ham_comm]

theorem ham_le_one (g h : Equiv.Perm Ω) : dH g h ≤ 1 := by
  unfold dH
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast h0)]
    exact_mod_cast card_le_univ _

/-- Distinct permutations differ in at least two points. -/
theorem ham_two_le_card {g h : Equiv.Perm Ω} (hgh : g ≠ h) :
    2 ≤ (univ.filter fun x => g x ≠ h x).card := by
  have : (univ.filter fun x => g x ≠ h x) = (h⁻¹ * g).support := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Equiv.Perm.mem_support, Equiv.Perm.mul_apply]
    constructor
    · intro hx hx'; apply hx; rw [Equiv.Perm.inv_eq_iff_eq] at hx'; exact hx'
    · intro hx hx'; apply hx; rw [Equiv.Perm.inv_eq_iff_eq]; exact hx'
  rw [this]
  apply Equiv.Perm.two_le_card_support_of_ne_one
  intro h1; apply hgh
  rw [inv_mul_eq_one] at h1; exact h1.symm

/-- If `dH g h < 2 / |Ω|` then `g = h`. -/
theorem ham_eq_of_lt {g h : Equiv.Perm Ω} (hlt : dH g h < 2 / Fintype.card Ω) : g = h := by
  by_contra hgh
  have h2 := ham_two_le_card hgh
  have hpos : (0 : ℝ) < Fintype.card Ω := by
    have : 0 < Fintype.card Ω := lt_of_lt_of_le (by norm_num) (h2.trans (card_le_univ _))
    exact_mod_cast this
  unfold dH at hlt
  rw [div_lt_div_iff_of_pos_right hpos] at hlt
  have : (2 : ℝ) ≤ (univ.filter fun x => g x ≠ h x).card := by exact_mod_cast h2
  linarith

end dH

variable {G : Type*} [Group G]

/-- A chunk of `G`: a finite subset containing `1` (with the partial multiplication induced by `G`). -/
def IsChunk (E : Finset G) : Prop := (1 : G) ∈ E

/-- `f : E → Sym_n` with `f 1 = 1` is an `ε`-morphism: `dH (f (x y)) (f x * f y) ≤ ε` whenever
`x, y, x y ∈ E` (Mathlib's product of permutations; see the module docstring). -/
def IsEpsMorphism (E : Finset G) (ε : ℝ) {n : ℕ} (f : G → Equiv.Perm (Fin n)) : Prop :=
  f 1 = 1 ∧ ∀ x ∈ E, ∀ y ∈ E, x * y ∈ E → dH (f (x * y)) (f x * f y) ≤ ε

/-- `f` is `(1 - ε)`-expansive on `E`: distinct elements of `E` have images at distance `≥ 1 - ε`. -/
def IsExpansive (E : Finset G) (ε : ℝ) {n : ℕ} (f : G → Equiv.Perm (Fin n)) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, x ≠ y → 1 - ε ≤ dH (f x) (f y)

/-- A `(1 - r⁻¹)`-expansive `r⁻¹`-morphism `E → Sym_n`. -/
def IsSoficModel (E : Finset G) (r : ℝ) {n : ℕ} (f : G → Equiv.Perm (Fin n)) : Prop :=
  IsEpsMorphism E r⁻¹ f ∧ IsExpansive E r⁻¹ f

/-- The degrees `n ≥ 1` admitting a `(1 - r⁻¹)`-expansive `r⁻¹`-morphism `E → Sym_n`. -/
def modelSizes (E : Finset G) (r : ℝ) : Set ℕ :=
  {n | 0 < n ∧ ∃ f : G → Equiv.Perm (Fin n), IsSoficModel E r f}

/-- Cornulier's sofic profile `σ_E(r)` (`⊤` if no model exists). -/
noncomputable def profile (E : Finset G) (r : ℝ) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' modelSizes E r)

/-! ### The paper's convention gives the same profile -/

/-- `ε`-morphism with the paper's product (`f x` followed by `f y`, i.e. Mathlib's `f y * f x`). -/
def IsEpsMorphismPaper (E : Finset G) (ε : ℝ) {n : ℕ} (f : G → Equiv.Perm (Fin n)) : Prop :=
  f 1 = 1 ∧ ∀ x ∈ E, ∀ y ∈ E, x * y ∈ E → dH (f (x * y)) (f y * f x) ≤ ε

/-- Model sizes in the paper's convention. -/
def modelSizesPaper (E : Finset G) (r : ℝ) : Set ℕ :=
  {n | 0 < n ∧ ∃ f : G → Equiv.Perm (Fin n), IsEpsMorphismPaper E r⁻¹ f ∧ IsExpansive E r⁻¹ f}

theorem modelSizesPaper_eq (E : Finset G) (r : ℝ) : modelSizesPaper E r = modelSizes E r := by
  ext n
  simp only [modelSizesPaper, modelSizes, IsSoficModel, IsEpsMorphism,
    IsEpsMorphismPaper, IsExpansive]
  constructor
  · rintro ⟨hn, f, ⟨h1, hm⟩, he⟩
    refine ⟨hn, fun g => (f g)⁻¹, ⟨by simp [h1], fun x hx y hy hxy => ?_⟩, fun x hx y hy hne => ?_⟩
    · rw [← mul_inv_rev, ham_inv]; exact hm x hx y hy hxy
    · rw [ham_inv]; exact he x hx y hy hne
  · rintro ⟨hn, f, ⟨h1, hm⟩, he⟩
    refine ⟨hn, fun g => (f g)⁻¹, ⟨by simp [h1], fun x hx y hy hxy => ?_⟩, fun x hx y hy hne => ?_⟩
    · rw [← mul_inv_rev, ham_inv]; exact hm x hx y hy hxy
    · rw [ham_inv]; exact he x hx y hy hne

/-! ### Basic facts about the profile -/

theorem profile_le_of_mem {E : Finset G} {r : ℝ} {n : ℕ} (h : n ∈ modelSizes E r) :
    profile E r ≤ n :=
  sInf_le ⟨n, h, rfl⟩

theorem mem_of_profile_eq {E : Finset G} {r : ℝ} {n : ℕ} (h : profile E r = n) :
    n ∈ modelSizes E r := by
  have hne : ((fun n : ℕ => (n : ℕ∞)) '' modelSizes E r).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    simp [profile, hc] at h
  obtain ⟨m, hm, hmeq⟩ := csInf_mem hne
  have h' : (m : ℕ∞) = n := hmeq.trans h
  have hmn : m = n := by exact_mod_cast h'
  rw [← hmn]; exact hm

/-- A lower bound valid for every model transfers to the profile (with `⊤` allowed). -/
theorem le_profile_of_forall {E : Finset G} {r : ℝ} {B : ℝ}
    (h : ∀ n ∈ modelSizes E r, B ≤ n) : ∀ m : ℕ, profile E r = m → B ≤ m :=
  fun m hm => h m (mem_of_profile_eq hm)

/-! ### Lemma `lem:floor` -/

/-- `E` embeds in a finite group: an injective map to a finite group sending `1 ↦ 1` and preserving
every product defined in `E`. -/
def EmbedsInFiniteGroup (E : Finset G) : Prop :=
  ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (ι : G → Q), ι 1 = 1 ∧ Set.InjOn ι E ∧
    ∀ x ∈ E, ∀ y ∈ E, x * y ∈ E → ι (x * y) = ι x * ι y

/-- Lemma `lem:floor`, first part: if `σ_E(r) < 2r` for some `r > 1`, then `E` embeds in a finite
group. -/
theorem embeds_of_profile_lt (E : Finset G) (r : ℝ) (hr : 1 < r) (n : ℕ)
    (hn : profile E r = n) (h2 : (n : ℝ) < 2 * r) : EmbedsInFiniteGroup E := by
  obtain ⟨hn0, f, ⟨hf1, hfm⟩, hfe⟩ := mem_of_profile_eq hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hrpos : (0 : ℝ) < r := by linarith
  have hsmall : r⁻¹ < 2 / (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin, lt_div_iff₀ hnpos, inv_mul_eq_div, div_lt_iff₀ hrpos]; linarith
  refine ⟨Equiv.Perm (Fin n), inferInstance, inferInstance, f, hf1, ?_, ?_⟩
  · intro x hx y hy hxy
    by_contra hne
    have h1 := hfe x hx y hy hne
    rw [hxy, ham_self] at h1
    have : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    linarith
  · intro x hx y hy hxy
    exact ham_eq_of_lt (lt_of_le_of_lt (hfm x hx y hy hxy) hsmall)

/-- The left regular representation of a finite group, transported to `Fin m`. -/
theorem profile_le_of_embeds (E : Finset G) (hE : EmbedsInFiniteGroup E) :
    ∃ C : ℕ, ∀ r : ℝ, 0 < r → profile E r ≤ C := by
  obtain ⟨Q, _, _, ι, hι1, hinj, hmul⟩ := hE
  let _ : Fintype Q := Fintype.ofFinite Q
  classical
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let L : Q → Equiv.Perm Q := fun g =>
    ⟨fun x => g * x, fun x => g⁻¹ * x, fun x => by simp, fun x => by simp⟩
  have hL : ∀ g h : Q, L (g * h) = L g * L h := by
    intro g h; ext x; simp [L, mul_assoc]
  have hL1 : L 1 = 1 := by ext x; simp [L]
  refine ⟨Fintype.card Q, fun r hr => profile_le_of_mem ⟨Fintype.card_pos, ?_⟩⟩
  refine ⟨fun g => e.permCongr (L (ι g)), ⟨?_, ?_⟩, ?_⟩
  · show e.permCongr (L (ι 1)) = 1
    rw [hι1, hL1]; ext k; simp
  · intro x hx y hy hxy
    dsimp only
    rw [hmul x hx y hy hxy, hL, Equiv.permCongr_mul, ham_self]
    exact le_of_lt (inv_pos.mpr hr)
  · intro x hx y hy hne
    dsimp only
    have hne' : ι x ≠ ι y := fun h => hne (hinj hx hy h)
    have hall : (univ.filter fun k : Fin (Fintype.card Q) =>
        e.permCongr (L (ι x)) k ≠ e.permCongr (L (ι y)) k) = univ := by
      apply filter_true_of_mem
      intro k _
      simp only [Equiv.permCongr_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      intro h
      apply hne'
      simpa [L] using h
    have hcard : (0 : ℝ) < Fintype.card (Fin (Fintype.card Q)) := by
      simp only [Fintype.card_fin]; exact_mod_cast Fintype.card_pos
    have : dH (e.permCongr (L (ι x))) (e.permCongr (L (ι y))) = 1 := by
      unfold dH; rw [hall, card_univ, div_self (ne_of_gt hcard)]
    rw [this]; linarith [inv_pos.mpr hr]

/-- Lemma `lem:floor`, "hence" part: `σ_E` is either bounded or at least `2r` for every `r > 1`
(the value `⊤` counts as `≥ 2r`). -/
theorem profile_bounded_or_ge (E : Finset G) :
    (∃ C : ℕ, ∀ r : ℝ, 1 < r → profile E r ≤ C) ∨
      (∀ r : ℝ, 1 < r → ∀ n : ℕ, profile E r = n → 2 * r ≤ n) := by
  by_cases h : ∃ r : ℝ, 1 < r ∧ ∃ n : ℕ, profile E r = n ∧ (n : ℝ) < 2 * r
  · obtain ⟨r, hr, n, hn, h2⟩ := h
    obtain ⟨C, hC⟩ := profile_le_of_embeds E (embeds_of_profile_lt E r hr n hn h2)
    exact Or.inl ⟨C, fun r' hr' => hC r' (by linarith)⟩
  · push Not at h
    exact Or.inr h

end Houghton
