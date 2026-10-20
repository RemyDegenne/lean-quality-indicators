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

theorem surjective_baseChangeMap_comp_baseChangeSpecIso
    {K A L : Type u} [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L] {X : Over (Spec (.of K))}
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of K)))
    (hf : Surjective f.left) :
    Surjective ((baseChangeMap (L := L) f).left ≫
      (baseChangeSpecIso K A L).hom) := by
  let _ : Surjective (baseChangeMap (L := L) f).left :=
    surjective_baseChangeMap f hf
  infer_instance

end
end AlgebraicGeometry
end
