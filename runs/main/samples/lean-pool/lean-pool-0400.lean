@[expose] public section

namespace LO

namespace Modal

open Entailment

infix:45 " ≺ " => Frame.Rel'

notation x:45 " ≺^[" n "] " y:46 => Frame.RelItr' n x y

namespace Formula

namespace Kripke

namespace ValidOnFrame

variable {F : Kripke.Frame}

protected lemma top_def : F ⊧ ⊤ := by simp [ValidOnFrame];

end ValidOnFrame
end Kripke
end Formula
end Modal
end LO
end
