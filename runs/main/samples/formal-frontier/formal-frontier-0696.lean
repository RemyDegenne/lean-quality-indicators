public section

open CategoryTheory Limits Opposite Topology

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

local instance globalSectionsAlgebraInstance
    (X : Over (Spec (.of K))) : Algebra K Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra K

theorem range_algebraMapOfToSpec_isFiniteEtale
    (X : Over (Spec (.of K))) {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    (algebraMapOfToSpec X f).range.IsFiniteEtale :=
  Algebra.IsFiniteEtale.of_surjective hB
    (algebraMapOfToSpec X f).rangeRestrict
    (AlgHom.rangeRestrict_surjective _)

end
end AlgebraicGeometry
end
