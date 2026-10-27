public section

open CategoryTheory Limits Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance componentGlobalSectionsAlgebra
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

local instance tensorProductRightAlgebra
    (A : Type u) [CommRing A] [Algebra k A] :
    Algebra K (A ⊗[k] K) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra

local instance baseChangeLocallyOfFiniteType
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (schemeBaseChange X (L := K)).hom := by
  change LocallyOfFiniteType
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

local instance baseChangeQuasiCompact
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (schemeBaseChange X (L := K)).hom := by
  change QuasiCompact
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

/-- The range of the scalar-extended selected component algebra. -/
abbrev baseChangedComponentSubalgebra
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Subalgebra K Γ((schemeBaseChange X (L := K)).left, ⊤) :=
  (componentScalarExtensionAlgHom (K := K) X).range

end
end AlgebraicGeometry
end
