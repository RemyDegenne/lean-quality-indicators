namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible

attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback

set_option autoImplicit false

p2m_open

universe u v

namespace R2LocIso

variable {S : Type u} [CommRing S]

theorem locIsoOnBase_mumfordBundle {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {𝓛 𝓛' : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h𝓛' : Scheme.Modules.IsInvertible 𝓛')
    (h : LocIsoOnBase f 𝓛 𝓛') :
    LocIsoOnBase (pullback.fst f f ≫ f) (mumfordBundle f L 𝓛) (mumfordBundle f L 𝓛') := by
  have hd := locIsoOnBase_dual f h𝓛 h𝓛' h
  have h1 : LocIsoOnBase (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (addMor f L)).obj 𝓛)
      ((Scheme.Modules.pullback (addMor f L)).obj 𝓛') :=
    LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) (addMor f L) (𝟙 _)
      (by rw [Category.comp_id]; exact addMor_over f L) h
  have h2 : LocIsoOnBase (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛))
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛')) :=
    LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) (pullback.fst f f) (𝟙 _)
      (by rw [Category.comp_id]) hd
  have h3 : LocIsoOnBase (pullback.fst f f ≫ f) ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛))
      ((Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛')) :=
    LocIsoOnBase.pullback_of_comp_eq (pullback.fst f f ≫ f) (pullback.snd f f) (𝟙 _)
      (by rw [Category.comp_id]; exact pullback.condition.symm) hd
  exact LocIsoOnBase.tensor h1 (LocIsoOnBase.tensor h2 h3)

end R2LocIso
end P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_mumfordBundle_of_isInvertible
