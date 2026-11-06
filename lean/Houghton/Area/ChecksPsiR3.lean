import Houghton.Area.Word
import Houghton.Area.Data.PsiR3

/-! Kernel check (`decide +kernel`: evaluation by the kernel only) of the certificate for `ψ(r3)`. -/

namespace Houghton.Word

theorem chk_psiR3 : checkPacked relW Houghton.Data.psiR3 (psiW (relW 2)) = true := by decide +kernel

end Houghton.Word
