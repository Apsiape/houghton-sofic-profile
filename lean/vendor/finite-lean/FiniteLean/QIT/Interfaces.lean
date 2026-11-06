import FiniteLean.QIT.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integral representation for the proof of joint convexity

`IntegralRep` is the integral representation used in the proof of joint convexity of relative entropy: for commuting positive
definite `L, R`, the quadratic form of `L (log L − log R)` is the improper integral over `s > 0` of
the quadratic form of `L (R + s L)⁻¹ L − (1 + s)⁻¹ L`, and that integrand is integrable.  It reduces,
in a joint eigenbasis, to `p log p − p log q = ∫₀^∞ (p²/(q + s p) − p/(1 + s)) ds` for `p, q > 0`.
Proved in `QIT/Integral.lean`; consumed by `QIT/JointConvexity.lean`.
-/

open scoped ComplexOrder

namespace QIT

def IntegralRep : Prop :=
  ∀ {m : Type} [Fintype m] [DecidableEq m] {L R : Matrix m m ℂ}, L.PosDef → R.PosDef →
    Commute L R → ∀ v : m → ℂ,
      MeasureTheory.IntegrableOn
        (fun s : ℝ => (dotProduct (star v) (Matrix.mulVec (L * (R + (s : ℂ) • L)⁻¹ * L - ((1 + s)⁻¹ : ℂ) • L) v)).re)
        (Set.Ioi 0) ∧
      (dotProduct (star v) (Matrix.mulVec (L * (mlog L - mlog R)) v)).re =
        ∫ s in Set.Ioi (0 : ℝ),
          (dotProduct (star v) (Matrix.mulVec (L * (R + (s : ℂ) • L)⁻¹ * L - ((1 + s)⁻¹ : ℂ) • L) v)).re

end QIT
