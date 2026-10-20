@[expose] public section

universe u v

namespace Ideal.Quotient

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

theorem coe_mkₐ_smulTop (J : Ideal R) :
    (Ideal.Quotient.mkₐ R (J.smulTop A) :
        A → A ⧸ (J • (⊤ : Submodule R A))) =
      ((J • (⊤ : Submodule R A)).mkQ : A → A ⧸ (J • (⊤ : Submodule R A))) :=
  rfl

end Ideal.Quotient
end
