public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open TopCat.Presheaf

universe u

namespace AlgebraicGeometry.Scheme

variable {ι : Type u}

noncomputable section

@[simp]
theorem sigmaPresheafObjIso_hom_apply (X : ι → Scheme.{u})
    (U : (∐ X : Scheme.{u}).Opens) (s : Γ(∐ X, U)) (i : ι) :
    (sigmaPresheafObjIso X U).hom s i = (Sigma.ι X i).app U s :=
  rfl

end
end AlgebraicGeometry.Scheme
end
