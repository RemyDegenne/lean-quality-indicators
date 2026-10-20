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

variable [IsLocalizedModule S f]

variable {S}

variable {f}

variable (f)

variable (S)

variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']

variable (g : N →ₗ[R] N') [IsLocalizedModule S g]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[R] Nₛ`. -/
noncomputable
def map : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[R] N') where
  toFun h := lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

end IsLocalizedModule
end IsLocalizedModule
end
