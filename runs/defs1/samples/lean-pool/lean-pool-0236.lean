@[expose] public section

namespace GaleStewartGame.BorelDet.Zero

open Stream'.Discrete Descriptive Tree Game PreStrategy

open CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section «Section1»

variable (H : PreLift hyp)

namespace WLLift

variable (H : WLLift hyp)

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftMediumVal : List (upA hyp) := H.liftShort.val ++ [⟨H.liftNode, H.liftTree⟩]

end WLLift
end «Section1»
end GaleStewartGame.BorelDet.Zero
end
