public section

set_option warningAsError true

open CategoryTheory Limits Opposite Set Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

local instance componentFibersGlobalSectionsAlgebra
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

theorem range_fiberι_toComponentScheme_eq_connectedComponent
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (x : (componentScheme X).left)
    (y : X.left) (hy : (toComponentScheme X).left y = x) :
    Set.range ((toComponentScheme X).left.fiberι x) =
      connectedComponent y := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let C := ConnectedComponents X.left → K
  have hC : Algebra.IsFiniteEtale K C := ⟨inferInstance, inferInstance⟩
  let g := componentFactor X hC (toConnectedComponentsSpec X)
  have htriangle : toComponentScheme X ≫ g =
      toConnectedComponentsSpec X :=
    toComponentScheme_comp_componentFactor X hC (toConnectedComponentsSpec X)
  have hinj : Function.Injective g.left := by
    intro a b hab
    obtain ⟨a', ha'⟩ := (surjective_toComponentScheme X).surj a
    obtain ⟨b', hb'⟩ := (surjective_toComponentScheme X).surj b
    have hcc : ConnectedComponents.mk a' = ConnectedComponents.mk b' := by
      apply (toConnectedComponentsSpec_apply_eq_iff X a' b').mp
      rw [← htriangle]
      change g.left ((toComponentScheme X).left a') =
        g.left ((toComponentScheme X).left b')
      simpa [ha', hb'] using hab
    have ht : (toComponentScheme X).left a' =
        (toComponentScheme X).left b' := by
      let _ : Module.Finite K (componentSubalgebra X) :=
        (componentSubalgebra_isFiniteEtale X).1
      let _ : Algebra.Etale K (componentSubalgebra X) :=
        (componentSubalgebra_isFiniteEtale X).2
      let _ : DiscreteTopology (componentScheme X).left := by
        change DiscreteTopology (Spec (.of (componentSubalgebra X)))
        exact Algebra.QuasiFinite.discreteTopology_primeSpectrum K
          (componentSubalgebra X)
      have himage : _root_.IsPreconnected
          ((toComponentScheme X).left '' connectedComponent a') :=
        isPreconnected_connectedComponent.image _
          (toComponentScheme X).left.continuous.continuousOn
      apply himage.subsingleton
      · exact ⟨a', mem_connectedComponent, rfl⟩
      · refine ⟨b', ?_, rfl⟩
        exact connectedComponent_eq_iff_mem.mp
          (ConnectedComponents.coe_eq_coe.mp hcc).symm
    exact ha'.symm.trans (ht.trans hb')
  rw [(toComponentScheme X).left.range_fiberι]
  ext z
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hz
    apply connectedComponent_eq_iff_mem.mp
    apply ConnectedComponents.coe_eq_coe.mp
    apply (toConnectedComponentsSpec_apply_eq_iff X z y).mp
    rw [← htriangle]
    change g.left ((toComponentScheme X).left z) =
      g.left ((toComponentScheme X).left y)
    rw [hz, hy]
  · intro hz
    have hconn : ConnectedComponents.mk z = ConnectedComponents.mk y :=
      ConnectedComponents.coe_eq_coe.mpr
        (connectedComponent_eq_iff_mem.mpr hz)
    have hf : (toConnectedComponentsSpec X).left z =
        (toConnectedComponentsSpec X).left y :=
      (toConnectedComponentsSpec_apply_eq_iff X z y).mpr hconn
    rw [← htriangle] at hf
    change g.left ((toComponentScheme X).left z) =
      g.left ((toComponentScheme X).left y) at hf
    rw [hy] at hf
    exact hinj hf

end
end AlgebraicGeometry
end
