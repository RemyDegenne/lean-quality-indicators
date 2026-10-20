@[expose] public section

universe u v w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory TopologicalSpace Opposite

section ContinuousFunctions

namespace TopCat

variable (X : TopCat.{v}) (R : TopCommRingCat.{v})

namespace continuousFunctions

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : TopCat.{u}ᵒᵖ) {R S : TopCommRingCat.{u}} (φ : R ⟶ S) :
    continuousFunctions X R ⟶ continuousFunctions X S := CommRingCat.ofHom
  { toFun g := g ≫ (forget₂ TopCommRingCat TopCat).map φ
    map_one' := by ext; exact φ.1.map_one
    map_zero' := by ext; exact φ.1.map_zero
    map_add' _ _ := by ext; exact φ.1.map_add _ _
    map_mul' _ _ := by ext; exact φ.1.map_mul _ _ }

end continuousFunctions
end TopCat
end ContinuousFunctions
end
end
