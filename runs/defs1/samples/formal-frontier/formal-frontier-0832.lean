@[expose] public section

universe uR uS uM uN

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

section IdealQuotient

variable {R : Type uR} [Ring R]

variable {M : Type uM} {N : Type uN}

variable [AddCommGroup M] [Module Rᵐᵒᵖ M]

variable [AddCommGroup N] [Module Rᵐᵒᵖ N]

/-- Quotienting a product of right modules by the action of a two-sided ideal
is the product of the corresponding quotient modules. -/
def idealQuotientProdLinearEquiv (I : Ideal R) [I.IsTwoSided] :
    IdealQuotient (M := M × N) I ≃ₗ[(R ⧸ I)ᵐᵒᵖ]
      IdealQuotient (M := M) I × IdealQuotient (M := N) I :=
  (idealQuotientLinearEquiv (M := M × N) I).symm.trans <|
    (prodLinearEquiv (f := Ideal.Quotient.mk I) (M := M) (N := N)).trans <|
      (idealQuotientLinearEquiv (M := M) I).prodCongr
        (idealQuotientLinearEquiv (M := N) I)

end IdealQuotient
end ModuleCat.RightExtension
end
