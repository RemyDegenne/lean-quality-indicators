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

/-- The positive cosine acting in source coordinates. -/
noncomputable def sourceCosine : U →L[ℂ] U := by
  let C : H →L[ℂ] H :=
    ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  have hCU : InvariantFor C U := by
    intro x hx
    apply U.starProjection_eq_self_iff.mp
    have hcomm := spectraCanonicalAbsoluteValue_commute_projection U V
    have happ := congrArg (fun T : H →L[ℂ] H => T x) hcomm.eq
    rw [mul_apply_eq_comp, mul_apply_eq_comp,
      Submodule.starProjection_eq_self_iff.mpr hx] at happ
    exact happ.symm
  exact C.restrict hCU

end DavisKahanGeometry
end
end Section4
end DavisKahan
end TauCeti
end
