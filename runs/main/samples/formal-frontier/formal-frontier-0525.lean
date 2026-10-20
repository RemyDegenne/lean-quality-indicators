@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M]

theorem coaction_injective (X : RightComodule R C M) : Function.Injective X.coaction := by
  intro m n h
  simpa only [X.rid_counit_coaction] using
    congrArg (fun t : M ⊗[R] C ↦
      TensorProduct.rid R M ((counit (R := R)).lTensor M t)) h

end RightComodule
end Coalgebra
end
