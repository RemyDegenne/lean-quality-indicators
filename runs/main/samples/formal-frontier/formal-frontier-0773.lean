@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry.AffineRelationQuotient

universe u

variable {R X : AffineScheme.{u}} (s t : R ⟶ X)

lemma quotientMap_faithfullyFlat_of_hasExpectedAlgebra
    (h : Ring.HasExpectedAlgebra
      ℤ Γ(X.obj, ⊤) Γ(R.obj, ⊤)
        s.hom.appTop.hom.toIntAlgHom t.hom.appTop.hom.toIntAlgHom) :
    (quotientMap s t).hom.appTop.hom.FaithfullyFlat := by
  let D := coordinateInvariantRing s t
  let _ : Algebra D Γ(X.obj, ⊤) := D.val.toRingHom.toAlgebra
  have hD : D.val.toRingHom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr h.1
  have hIso : (quotientInvariantIso s t).hom.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective
      (ConcreteCategory.bijective_of_isIso (quotientInvariantIso s t).hom)
  have hcomp := RingHom.FaithfullyFlat.stableUnderComposition
    (quotientInvariantIso s t).hom.hom D.val.toRingHom hIso hD
  rw [← quotientInvariantIso_hom_comp s t]
  exact hcomp

end AlgebraicGeometry.AffineRelationQuotient
end
end
