import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

namespace Houghton
noncomputable def dH {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (g h : Equiv.Perm Ω) : ℝ :=
  ((Finset.univ.filter fun x => g x ≠ h x).card : ℝ) / Fintype.card Ω

end Houghton
