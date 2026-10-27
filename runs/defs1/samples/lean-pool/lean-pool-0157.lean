@[expose] public section

universe u v

variable {F A : Type u}

variable [Field F] [Ring A] [Algebra F A]

variable [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A]

variable (B : Subalgebra F A) [IsSimpleRing B]

open Module TensorProduct

namespace centralizerIsSimple.aux

open FiniteDimensional

/-- The left tensor inclusion as an algebra equivalence onto its range. -/
noncomputable def auxLeft (B : Subalgebra F A) (C : Type u) [Ring C] [Algebra F C] :
    B ⊗[F] C ≃ₐ[F] (Algebra.TensorProduct.map B.val (AlgHom.id F C)).range :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInjective _ <| by
      change Function.Injective <| LinearMap.rTensor _ _
      apply Module.Flat.rTensor_preserves_injective_linearMap
      exact Subtype.val_injective)
    (by
      ext
      erw [LinearEquiv.ofInjective_apply])
    (by
      intro x y
      ext
      erw [LinearEquiv.ofInjective_apply]
      change Algebra.TensorProduct.map _ _ _ = _
      rw [map_mul]
      rfl)

end centralizerIsSimple.aux
end
