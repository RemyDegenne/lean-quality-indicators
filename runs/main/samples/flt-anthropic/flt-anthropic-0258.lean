namespace P2MW.S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

section P13_E_INTEGRAL

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

namespace P2MMultE

open scoped TensorProduct

section IntegralPts

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]

variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]

variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]

variable {S : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

theorem β_apply (h : IPtHyp S) (ψ : ↥(ES h) →ₐ[O] L) (θ : ↥(CSub h.toPtHyp)) :
    β h ψ θ = liftS F ψ ((genericFibreES h).symm θ) := by
  rw [β, Equiv.trans_apply, AlgEquiv.arrowCongr_apply, liftSEquiv_apply]
  rfl

end IntegralPts
end P2MMultE
end P13_E_INTEGRAL
end P2MW.S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction
