public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Main

noncomputable section

theorem e6FrameRho1_coe (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((e6FrameRho1 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) =
      e6FrameMoveElt K * ((e6FrameRho0 K A : adjointGroup .E6 K) : ModGL Tag.E6 K) *
        (e6FrameMoveElt K)⁻¹ :=
  rfl

end
end Main
end CFSG.StandardType
end
