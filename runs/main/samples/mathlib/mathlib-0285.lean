@[expose] public section

open LinearMap (ker range)

universe u v w u'

@[inherit_doc]
notation:25 M " →SL[" σ "] " M₂ => ContinuousLinearMap σ M M₂

@[inherit_doc]
notation:25 M " →L[" R "] " M₂ => ContinuousLinearMap (RingHom.id R) M M₂

namespace ContinuousLinearMap

section Semiring

variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃} {M₁ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] {M'₁ : Type*} [TopologicalSpace M'₁] [AddCommMonoid M'₁] {M₂ : Type*}
  [TopologicalSpace M₂] [AddCommMonoid M₂] {M₃ : Type*} [TopologicalSpace M₃] [AddCommMonoid M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [AddCommMonoid M₄] [Module R₁ M₁] [Module R₁ M'₁]
  [Module R₂ M₂] [Module R₃ M₃]

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

@[inherit_doc comp]
infixr:80 " ∘L " =>
  @ContinuousLinearMap.comp _ _ _ _ _ _ (RingHom.id _) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _
    _ _ _ _ RingHomCompTriple.ids

@[inherit_doc comp]
infixr:90 " ∘SL " =>
  ContinuousLinearMap.comp

@[simp, norm_cast]
theorem toLinearMap_mul (f g : M₁ →L[R₁] M₁) : (↑(f * g) : M₁ →ₗ[R₁] M₁) = f * g :=
  rfl

end Semiring
end ContinuousLinearMap
end
