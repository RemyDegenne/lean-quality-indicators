@[expose] public section

open Module nonZeroDivisors

variable (A K L L₂ L₃ B B₂ B₃ : Type*)

variable [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]

variable [Algebra A B] [Algebra A B₂] [Algebra A B₃]

variable [Field K] [Field L] [Field L₂] [Field L₃]

variable [Algebra A K] [IsFractionRing A K]

variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]

variable [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]

variable [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

variable [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]

variable [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]

section galois

variable [Algebra.IsAlgebraic K L]

section galLift

variable {A B B₂ B₃}

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem galLift_galRestrict' (σ : L →ₐ[K] L₂) :
    galLift K L L₂ (galRestrict' A B B₂ σ) = σ :=
  have := (IsFractionRing.injective A K).isDomain
  have := IsIntegralClosure.isLocalization A K L B
  AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B A⁰)
    <| RingHom.ext fun x ↦ by simp [galRestrict', Subalgebra.algebraMap_eq, galLift]

end galLift
end galois
end
