import Houghton.Area.Word
import Houghton.Area.Data.Small

/-! Kernel checks (`decide +kernel`: evaluation by the kernel only) of the small certificates. -/

namespace Houghton.Word
open Houghton.Data

theorem chk_A2 : checkPacked relW A2 (commW (sigmaW 0) (sigmaW 2)) = true := by decide +kernel
theorem chk_E0 : checkPacked relW E0 (commW (sigmaW 0) tW) = true := by decide +kernel
theorem chk_U1 : checkPacked relW U1 (tauW 1 ++ invW (sigmaW 1)) = true := by decide +kernel
theorem chk_E1 : checkPacked relW E1 (commW (sigmaW 1) tW) = true := by decide +kernel
theorem chk_U2 : checkPacked relW U2 (tauW 2 ++ invW (sigmaW 2)) = true := by decide +kernel
theorem chk_B0 : checkPacked relW B0 (commW [4] (sigmaW 1 ++ sigmaW 0 ++ [2])) = true := by decide +kernel
theorem chk_B2 : checkPacked relW B2 (commW (sigmaNegW 2) [2]) = true := by decide +kernel
theorem chk_A3 : checkPacked relW A3 (commW (sigmaW 0) (sigmaW 3)) = true := by decide +kernel
theorem chk_A4 : checkPacked relW A4 (commW (sigmaW 0) (sigmaW 4)) = true := by decide +kernel
theorem chk_E2 : checkPacked relW E2 (commW (sigmaW 2) tW) = true := by decide +kernel
theorem chk_U3 : checkPacked relW U3 (tauW 3 ++ invW (sigmaW 3)) = true := by decide +kernel
theorem chk_B3 : checkPacked relW B3 (commW (sigmaNegW 3) [2]) = true := by decide +kernel
theorem chk_A5 : checkPacked relW A5 (commW (sigmaW 0) (sigmaW 5)) = true := by decide +kernel
theorem chk_A6 : checkPacked relW A6 (commW (sigmaW 0) (sigmaW 6)) = true := by decide +kernel
theorem chk_E3 : checkPacked relW E3 (commW (sigmaW 3) tW) = true := by decide +kernel
theorem chk_N4 : checkPacked relW N4 ([3] ++ rhoW ++ [2] ++ invW (symW RpS)) = true := by decide +kernel
theorem chk_commXRho : checkPacked relW commXRho (commW [4] rhoW) = true := by decide +kernel
theorem chk_CONV : checkPacked relW CONV (psiW [4] ++ invW PiW) = true := by decide +kernel
theorem chk_BRAID : checkPacked relW BRAID
    (sigmaW 1 ++ sigmaW 0 ++ sigmaW 1 ++ invW (sigmaW 0 ++ sigmaW 1 ++ sigmaW 0)) = true := by
  decide +kernel
theorem chk_psiR1 : checkPacked relW psiR1 (psiW (relW 0)) = true := by decide +kernel
theorem chk_psiR4 : checkPacked relW psiR4 (psiW (relW 3)) = true := by decide +kernel
theorem chk_psiRho : checkPacked relW psiRho (psiW rhoW ++ invW (symW RS)) = true := by decide +kernel

end Houghton.Word
