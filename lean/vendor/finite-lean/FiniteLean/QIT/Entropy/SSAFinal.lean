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
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Module
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.List.Induction
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Matrix.PosDef
import FiniteLean.QIT.Entropy.SSAUnconditional
import FiniteLean.QIT.RelEntConvex
import FiniteLean.QIT.Integral

namespace Houghton

theorem qit_relEntJointlyConvex : QIT_RelEntJointlyConvex := by
  intro n _ _ ρ₁ ρ₂ σ₁ σ₂ h₁ h₂ k₁ k₂ t ht0 ht1
  exact QIT.relEnt_jointlyConvex_of QIT.integralRep h₁ h₂ k₁ k₂ ht0 ht1

theorem qit_relEntUnitaryInvariant : QIT_RelEntUnitaryInvariant := by
  intro n _ _ U ρ σ hρ hσ
  exact QIT.relEnt_unitary_conj U hρ hσ

/-- Strong subadditivity for commuting pinchings, unconditionally. -/
theorem qit_commutingPinchingSSA : QIT_CommutingPinchingSSA.{0} :=
  qit_commutingPinchingSSA_of qit_relEntJointlyConvex qit_relEntUnitaryInvariant


end Houghton
