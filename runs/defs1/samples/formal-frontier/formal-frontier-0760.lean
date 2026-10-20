@[expose] public section

noncomputable section

open CategoryTheory Category Limits Preadditive

namespace CochainComplex.RelativePath

attribute [local instance] ComplexShape.decidableRelSymm

variable {C : Type*} [Category* C] [Preadditive C]

variable [HasBinaryBiproducts C]

variable [HasPullbacks C]

variable {B₁ B A : CochainComplex C ℤ}

/-- A chosen homotopy gives a strict lift into the *same* fixed-arrow object. -/
def lift (f : B₁ ⟶ B) (u : A ⟶ B₁) (v : A ⟶ B)
    (h : Homotopy (u ≫ f) v) : A ⟶ obj f :=
  pullback.lift u (HomologicalComplex.pathObject.lift (u ≫ f) v h) (by simp)

end CochainComplex.RelativePath
end
end
