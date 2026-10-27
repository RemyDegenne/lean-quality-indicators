set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

variable (F : Type*) [Field F] [Algebra L F]

variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]

namespace ComponentChart

section DegenerateMember

variable (L : Type*) [Field L] (F : Type*) [Field F] [Algebra L F]

attribute [local instance] ConstantReduction.ofTopAlgebra

def ofTop : ComponentChart (⊤ : ValuationSubring L) F F :=
  ofConstantReduction (ConstantReduction.ofTop L F) (ConstantReduction.isPointwise_ofTop L F)

end DegenerateMember
end ComponentChart
end AlgebraicCurve
end
