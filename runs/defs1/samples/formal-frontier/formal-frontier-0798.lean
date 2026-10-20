@[expose] public section

open CategoryTheory TopologicalSpace

open scoped Polynomial

noncomputable section

namespace AlgebraicGeometry.EquivalenceRelation

universe u

open AlgebraicGeometry

universe w

/-- Affine coordinates preserve an internal scheme equivalence relation. -/
def appTop {R X : Scheme.{w}} {p₁ p₂ : R ⟶ X}
    [IsAffine R] [IsAffine X] (h : EquivalenceRelation p₁ p₂) :
    EquivalenceRelation (Spec.map p₁.appTop) (Spec.map p₂.appTop) := by
  have hp₁ : R.isoSpec.inv ≫ p₁ ≫ X.isoSpec.hom = Spec.map p₁.appTop := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hp₂ : R.isoSpec.inv ≫ p₂ ≫ X.isoSpec.hom = Spec.map p₂.appTop := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Iso.symm_hom, hp₁, hp₂] using
    CategoryTheory.EquivalenceRelation.transport h R.isoSpec.symm X.isoSpec

end AlgebraicGeometry.EquivalenceRelation
end
end
