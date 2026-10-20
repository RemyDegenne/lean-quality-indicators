namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace P2mLBGlue

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

section Cocycle

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsSeparated f]
  (G : OModulePresheaf f)
  {κ : Type u} (U : κ → X.affineOpens) (g : ∀ i, G.obj (U i).1)
  (hg : ∀ (i : κ) (V : X.affineOpens) (hV : V.1 ≤ (U i).1),
    Function.Bijective fun b : Γ(X, V.1) => b • G.res hV (g i))

theorem cocycle_u (i j : κ) : (cocycle f G U g hg).u i j = uu f G U g hg i j := rfl

end Cocycle
end P2mLBGlue
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_forall_bijective_smul_res_of_affHom_pushforward
