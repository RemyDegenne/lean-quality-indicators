public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.OuterAutomorphisms

theorem piR_lM
    {l : onX → onL} (hl : ∀ x, piM (lM l x) = x) (x : onX) :
    piR (lM l x) = ⟨x, onX_le_RM x.2⟩ := Subtype.ext (hl x)

end CFSG.Sporadic.ONOddCore
end
