import Houghton.Area.Word
import Houghton.Area.Data.PsiR2

/-! Kernel check (`decide +kernel`: evaluation by the kernel only) of the certificate for `ψ(r2)`. -/

namespace Houghton.Word

theorem chk_psiR2 : checkPacked relW Houghton.Data.psiR2 (psiW (relW 1)) = true := by decide +kernel

end Houghton.Word
