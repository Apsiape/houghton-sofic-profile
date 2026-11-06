import Houghton.Area.WordAux
import Houghton.Area.Data.Aux107

/-! Kernel checks (`decide +kernel`: evaluation by the kernel only) of the auxiliary certificates used for
Theorem `thm:area-weighted`: the images `D(r_i)` (`i ∈ I`) and the four rules `d(t), d(q), o(t), o(q)`,
together with their weighted costs. -/

namespace Houghton.Word
open Houghton.Data

theorem chk_wD1 : checkPacked relWA wD1 (psiW (relWA 0)) = true := by decide +kernel
theorem chk_wD3 : checkPacked relWA wD3 (psiW (relWA 1)) = true := by decide +kernel
theorem chk_wD4 : checkPacked relWA wD4 (psiW (relWA 2)) = true := by decide +kernel
theorem chk_wD5 : checkPacked relWA wD5 (psiW (relWA 3)) = true := by decide +kernel
theorem chk_wD6 : checkPacked relWA wD6 (psiW (relWA 4)) = true := by decide +kernel
theorem chk_wdt : checkPacked relWA wdt (psiW tW ++ invW (symQ DTq)) = true := by decide +kernel
theorem chk_wdq : checkPacked relWA wdq (psiW qW ++ invW (symQ DQq)) = true := by decide +kernel
theorem chk_wot : checkPacked relWA wot ([3] ++ psiW tW ++ [2] ++ invW (symQ OTq)) = true := by
  decide +kernel
theorem chk_woq : checkPacked relWA woq ([3] ++ psiW qW ++ [2] ++ invW (symQ OQq)) = true := by
  decide +kernel

/-- The rows of the substitution matrix, weighted: `M w ≤ 107 w`. -/
theorem wsum_D : wsumA wD1 ≤ 107 * wtA 0 ∧ wsumA wD3 ≤ 107 * wtA 1 ∧ wsumA wD4 ≤ 107 * wtA 2 ∧
    wsumA wD5 ≤ 107 * wtA 3 ∧ wsumA wD6 ≤ 107 * wtA 4 := by decide +kernel

/-- The four rule costs are at most `2315`. -/
theorem wsum_rules : wsumA wdt ≤ 2315 ∧ wsumA wdq ≤ 2315 ∧ wsumA wot ≤ 2315 ∧
    wsumA woq ≤ 2315 := by decide +kernel

end Houghton.Word
