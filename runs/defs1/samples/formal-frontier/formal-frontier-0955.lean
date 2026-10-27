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

/-- A qc locally-finite-type scheme maps canonically to one copy of the base
point for each of its connected components. -/
@[expose]
noncomputable def toConnectedComponentsSpec
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    X ⟶ specOver k (ConnectedComponents X.left → k) := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let f : X.left ⟶ Spec (.of (ConnectedComponents X.left → k)) :=
    X.left.toConnectedComponentCoproduct X.hom ≫
      sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of k)
  refine Over.homMk f ?_
  change f ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (ConnectedComponents X.left → k))) = X.hom
  rw [← cancel_epi X.left.connectedComponentSigmaIso.hom]
  apply Sigma.hom_ext
  intro c
  dsimp only [f]
  simp only [X.left.connectedComponentSigmaIso_hom_ι_assoc]
  change (X.left.connectedComponentOpen c).ι ≫
      X.left.toConnectedComponentCoproduct X.hom ≫
        (sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of k) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap k (ConnectedComponents X.left → k)))) = _
  rw [Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct_assoc]
  rw [ι_sigmaSpec_assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom
        (algebraMap k (ConnectedComponents X.left → k)) ≫
      CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : ConnectedComponents X.left ↦ k) c) =
      𝟙 (CommRingCat.of k) by ext x; rfl]
  simp

end
end AlgebraicGeometry
end
