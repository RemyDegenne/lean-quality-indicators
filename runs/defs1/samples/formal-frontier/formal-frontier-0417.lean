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

/-- The factor from the component scheme to a finite-etale affine target. -/
@[expose]
def componentFactor
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    componentScheme X ⟶ specOver K B :=
  specOverMap (componentFactorAlgHom X hB f)

end
end AlgebraicGeometry
end
