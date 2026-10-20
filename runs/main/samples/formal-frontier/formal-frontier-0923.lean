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

theorem componentBaseChangeComparisonAlgHom_surjective
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (componentBaseChangeComparisonAlgHom (K := K) X) := by
  let P := componentSubalgebra X
  let XK := schemeBaseChange X (L := K)
  let Q := componentSubalgebra XK
  let _ : Algebra K (P ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let f := componentBaseChangeComparisonAlgHom (K := K) X
  let _ : Module.Finite k P := (componentSubalgebra_isFiniteEtale X).1
  let _ : Module.Finite K (P ⊗[k] K) :=
    (componentAlgebraTensor_isFiniteEtale (K := K) X).1
  let _ : Module.Finite K Q := (componentSubalgebra_isFiniteEtale XK).1
  have hsource : Module.finrank K (P ⊗[k] K) = Module.finrank k P := by
    calc
      Module.finrank K (P ⊗[k] K) = Module.finrank K (K ⊗[k] P) :=
        (Algebra.TensorProduct.commRight k K P).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k P := Module.finrank_baseChange
  have htarget : Module.finrank K Q = Module.finrank k P := by
    calc
      Module.finrank K Q = Nat.card (ConnectedComponents
          (schemeBaseChange XK (L := SeparableClosure K)).left) :=
        componentSubalgebra_finrank_eq_natCard_separableClosure XK
      _ = Nat.card (ConnectedComponents
          (schemeBaseChange X (L := SeparableClosure k)).left) :=
        (natCard_connectedComponents_separableClosures_eq (K := K) X).symm
      _ = Module.finrank k P :=
        (componentSubalgebra_finrank_eq_natCard_separableClosure X).symm
  have hfinrank : Module.finrank K (P ⊗[k] K) = Module.finrank K Q :=
    hsource.trans htarget.symm
  have hinjective : Function.Injective f.toLinearMap :=
    componentBaseChangeComparisonAlgHom_injective (K := K) X
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hfinrank).mp hinjective

end
end AlgebraicGeometry
end
