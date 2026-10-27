public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

local instance tensorLocallyOfFiniteType
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : LocallyOfFiniteType (pullback.fst X.hom Y.hom) := inferInstance
  let _ : LocallyOfFiniteType (fst X Y).left := by
    change LocallyOfFiniteType (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

local instance tensorQuasiCompact
    (X Y : Over (Spec (.of K))) [QuasiCompact X.hom]
    [QuasiCompact Y.hom] : QuasiCompact (X ⊗ Y).hom := by
  rw [← (fst X Y).w]
  let _ : QuasiCompact (pullback.fst X.hom Y.hom) := inferInstance
  let _ : QuasiCompact (fst X Y).left := by
    change QuasiCompact (pullback.fst X.hom Y.hom)
    infer_instance
  infer_instance

local instance sourceCompactSpace (Z : Over (Spec (.of K)))
    [QuasiCompact Z.hom] : CompactSpace Z.left :=
  QuasiCompact.compactSpace_of_compactSpace Z.hom

local instance sourceIsLocallyNoetherian (Z : Over (Spec (.of K)))
    [LocallyOfFiniteType Z.hom] : IsLocallyNoetherian Z.left :=
  LocallyOfFiniteType.isLocallyNoetherian Z.hom

local instance sourceIsNoetherian (Z : Over (Spec (.of K)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] : IsNoetherian Z.left := ⟨⟩

local instance baseChangeLocallyOfFiniteTypeProduct
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (schemeBaseChange X (L := L)).hom := by
  change LocallyOfFiniteType
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  infer_instance

local instance baseChangeQuasiCompactProduct
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (schemeBaseChange X (L := L)).hom := by
  change QuasiCompact
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  infer_instance

/-- The canonical component scheme of a binary fibre product is the fibre
product of the component schemes, as in J. S. Milne, *Algebraic Groups*
(2017), Proposition 1.30(b). -/
noncomputable def componentProductIso
    (X Y : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    componentScheme (X ⊗ Y) ≅ componentScheme X ⊗ componentScheme Y :=
  (specOverIsoOfAlgEquiv (productFactorAlgEquiv X Y)).trans
    (componentProductModelIso X Y).symm

end
end AlgebraicGeometry
end
