import Houghton.Area.Word
import Houghton.Area.Data.PsiR5

/-! Kernel check (`decide +kernel`: evaluation by the kernel only) of the certificate for `ψ(r5)`. -/

namespace Houghton.Word

theorem chk_psiR5 : checkPacked relW Houghton.Data.psiR5 (psiW (relW 4)) = true := by decide +kernel

end Houghton.Word
