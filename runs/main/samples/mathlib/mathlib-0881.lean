@[expose] public section

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

namespace Submodule

lemma restrictScalars_localized' :
    (localized' S p f M').restrictScalars R = localized₀ p f M' :=
  rfl

end Submodule
end
