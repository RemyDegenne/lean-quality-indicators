@[expose] public section

open Module

section IsLocalizedModule

universe u v

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']

variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]

variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']

variable (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

namespace IsLocalizedModule

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']

variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]

variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']

variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]

variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']

variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

variable {R A M M' : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [IsLocalization S A]

attribute [local instance] LocalizedModule.moduleOfIsLocalization in
/-- If `M'` is the localization of `M` at `S` and `A = S⁻¹R`, then `M'` is an `A`-module. -/
@[reducible] noncomputable def module (f : M →ₗ[R] M') [IsLocalizedModule S f] : Module A M' :=
  (IsLocalizedModule.iso S f).symm.toAddEquiv.module A

end IsLocalizedModule
end IsLocalizedModule
end
