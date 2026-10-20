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

theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s, Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

end IsLocalizedModule
end IsLocalizedModule
end
