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

/-- The canonical scalar-extension map from the coordinate algebra of the
base-changed component scheme to the global sections of the base-changed
source scheme.

The source is `componentSubalgebra X ⊗[k] K`, matching
`baseChangeSpecOverIso`; internally the global-sections equivalence
uses the factor-reversed tensor product. -/
noncomputable def componentScalarExtensionAlgHom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra X ⊗[k] K →ₐ[K]
      Γ((schemeBaseChange X (L := K)).left, ⊤) :=
  (componentGlobalSectionsBaseChangeEquiv (K := K) X).toAlgHom.comp
    ((SeparableClosureDescent.scalarExtensionMap
      (K := K) (componentSubalgebra X)).comp
        (Algebra.TensorProduct.commRight k K (componentSubalgebra X)).symm.toAlgHom)

end
end AlgebraicGeometry
end
