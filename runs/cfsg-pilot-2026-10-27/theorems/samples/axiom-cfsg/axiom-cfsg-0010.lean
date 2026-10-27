@[expose] public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native Matrix

theorem lyPhiP_apply (g : J) : (lyPhiP g : Equiv.Perm (Fin lyN)) = lyPhi g := rfl

end CFSG.RankThree.Native
end
