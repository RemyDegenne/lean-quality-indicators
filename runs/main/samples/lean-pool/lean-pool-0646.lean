@[expose] public section

open TauCeti.DavisKahan.Angle

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

namespace Section4

open ExactSinTheta

open DavisKahanExt

open TauCeti.DavisKahan

open Foundation

open Module (finrank)

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section DavisKahanGeometry

universe w

variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

local instance sourceCompleteSpace : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

theorem sourceRestrictedDisplacement_extendDomainByZero
    (T : H →L[ℂ] H) :
    sourceRestrictedDisplacement U T ∘L U.subtypeL.adjoint =
      (1 - T) ∘L U.starProjection := by
  ext x
  simp [sourceRestrictedDisplacement, Submodule.adjoint_subtypeL]

end DavisKahanGeometry
end
end Section4
end DavisKahan
end TauCeti
end
