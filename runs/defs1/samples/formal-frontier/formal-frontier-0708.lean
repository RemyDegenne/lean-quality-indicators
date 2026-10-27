public section

open CategoryTheory Limits Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

local instance componentGlobalSectionsAlgebra'
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

local instance tensorProductRightAlgebra'
    {F L A : Type u} [CommRing F] [CommRing L] [Algebra F L]
    [CommRing A] [Algebra F A] :
    Algebra L (A ⊗[F] L) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra

local instance baseChangeLocallyOfFiniteType'
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (schemeBaseChange X (L := K)).hom := by
  change LocallyOfFiniteType
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

local instance baseChangeQuasiCompact'
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (schemeBaseChange X (L := K)).hom := by
  change QuasiCompact
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

/-- The canonical categorical base-change isomorphism for arbitrary field
extension, as in J. S. Milne, *Algebraic Groups* (2017),
Proposition 1.30(a). -/
noncomputable def componentBaseChangeIso
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ≅
      schemeBaseChange (componentScheme X) (L := K) :=
  (componentBaseChangeComparisonModelIso (K := K) X).trans
    (componentSchemeBaseChangeModelIso (K := K) X).symm

end
end AlgebraicGeometry
end
