import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Defs
import FiniteLean.QIT.Entropy.Scalar
import Mathlib.Analysis.Matrix.Spectrum

universe u
namespace Houghton
open Finset Equiv Matrix ComplexConjugate
section QIT

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- von Neumann entropy (nats) `S(A) = ∑ᵢ η(λᵢ)` of a Hermitian matrix (`0` if not Hermitian). -/
noncomputable def vN (A : Matrix ι ι ℂ) : ℝ := by
  classical
  exact if h : A.IsHermitian then ∑ i, ent (h.eigenvalues i) else 0

/-- Density matrix: Hermitian, positive semidefinite, unit trace. -/
def IsDensity (ρ : Matrix ι ι ℂ) : Prop :=
  ρ.IsHermitian ∧ (∀ v : ι → ℂ, 0 ≤ (star v ⬝ᵥ (ρ *ᵥ v)).re) ∧ ρ.trace = 1

/-- A complete family of pairwise orthogonal orthogonal projections. -/
structure IsProjFamily {α : Type} [Fintype α] [DecidableEq α] (P : α → Matrix ι ι ℂ) :
    Prop where
  herm : ∀ a, (P a)ᴴ = P a
  orth : ∀ a b, P a * P b = if a = b then P a else 0
  sum_one : ∑ a, P a = 1

/-- The pinching (conditional expectation) `X ↦ ∑ₐ Pₐ X Pₐ`. -/
noncomputable def pinch {α : Type} [Fintype α] (P : α → Matrix ι ι ℂ) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  ∑ a, P a * X * P a

/-- The composition `Π_{P 0} ∘ ⋯ ∘ Π_{P (m-1)}` of pinchings. -/
noncomputable def pinchAll {α : Type} [Fintype α] :
    ∀ {m : ℕ}, (Fin m → α → Matrix ι ι ℂ) → Matrix ι ι ℂ → Matrix ι ι ℂ
  | 0, _, X => X
  | _ + 1, P, X => pinch (P 0) (pinchAll (fun k => P k.succ) X)

end QIT

/-- **Textbook input: strong subadditivity for commuting pinchings.** For pairwise commuting
complete families of orthogonal projections `P₀, …, P_{m-1}` and a density matrix `ρ`, the entropy
gain of the composed pinching is at most the sum of the individual entropy gains:
`S(Π₀ ⋯ Π_{m-1} ρ) - S(ρ) ≤ ∑ₖ (S(Πₖ ρ) - S(ρ))`.
This is strong subadditivity of von Neumann entropy in its commuting-conditional-expectation
("commuting square") form: E. H. Lieb, M. B. Ruskai, J. Math. Phys. 14 (1973) 1938; see also
D. Petz, *Quantum Information Theory and Quantum Statistics* (Springer 2008), and Nielsen–Chuang,
Thm. 11.15.  Derivation: for a pinching `S(Πσ) - S(σ) = D(σ‖Πσ)`, and since the pinchings commute,
`D(Eρ ‖ Π Eρ) = D(Eρ ‖ E Πρ) ≤ D(ρ‖Πρ)` for `E = Π₀ ⋯ Π_{k-1}` by monotonicity of relative entropy
under channels (Lindblad 1975, Uhlmann 1977); telescope over `k`. -/
def QIT_CommutingPinchingSSA : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (α : Type) [Fintype α] [DecidableEq α] (m : ℕ)
    (P : Fin m → α → Matrix ι ι ℂ), (∀ k, IsProjFamily (P k)) →
    (∀ k l, k ≠ l → ∀ a b, P k a * P l b = P l b * P k a) →
    ∀ ρ : Matrix ι ι ℂ, IsDensity ρ →
      vN (pinchAll P ρ) + m * vN ρ ≤ ∑ k, vN (pinch (P k) ρ) + vN ρ


end Houghton
