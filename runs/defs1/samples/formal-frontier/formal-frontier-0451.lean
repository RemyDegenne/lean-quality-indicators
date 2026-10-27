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

/-- The standard affine identification of the scalar extension of `Spec A`
with the spectrum of `A ⊗[K] L`. -/
@[expose]
def baseChangeSpecIso
    (K A L : Type u) [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L] :
    (schemeBaseChange ((Spec (.of A)).asOver (Spec (.of K)))
      (L := L)).left ≅ Spec (.of (A ⊗[K] L)) :=
  pullbackSpecIso K A L

end
end AlgebraicGeometry
end
