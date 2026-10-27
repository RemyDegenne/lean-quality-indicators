namespace P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv

set_option autoImplicit false

open scoped TensorProduct

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

section P13_T5_INTEGRAL

namespace P2MMultE

open scoped TensorProduct

section IntegralPts

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]

variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]

variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]

variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable def dhat (h : IPtHyp S) (ν : ↥S) : L ⊗[O] ↥(ES h) := (Ω h).symm (dElt h.toPtHyp ν)

end IntegralPts
end P2MMultE
end P13_T5_INTEGRAL
end P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv
