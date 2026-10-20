@[expose] public section

open LinearMap (ker range)

namespace ContinuousLinearMap

section Restrict

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
  [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₃] [Module R₃ M₃]

lemma coe_domRestrict (f : M₁ →SL[σ₁₂] M₂) (p : Submodule R₁ M₁) :
    ⇑(f.domRestrict p) = Set.domRestrict p f :=
  rfl

end Restrict
end ContinuousLinearMap
end
