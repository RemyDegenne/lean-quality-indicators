public section

open scoped TensorProduct

namespace TauCeti.CompletedTensorWords

universe uR uM uN uP uQ

variable {R : Type uR} [CommSemiring R]
  {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Include an algebraic tensor of finite words into the product of its bidegrees. -/
noncomputable def tensorInclusion :
    TensorWords R M ⊗[R] TensorWords R N →ₗ[R] TensorProduct R M N :=
  LinearMap.pi fun p ↦ LinearMap.pi fun q ↦
    TensorProduct.map (TensorWords.component R M p) (TensorWords.component R N q)

end TauCeti.CompletedTensorWords
end
