namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_pullback_iso_pullback_of_comp_toProj_eq

attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace INVARSol

variable {R : Type u} [CommRing R] {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {𝓝 : X.Modules} {N : ℕ}
  (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N)

variable (T : X' ⟶ X)

noncomputable def a (i : Fin (N + 1)) (W : X'.Opens) : Γ((Scheme.Modules.pullback T).obj 𝓝, W) :=
  ((Scheme.Modules.pullback T).obj 𝓝).presheaf.map (homOfLE (le_top : W ≤ T ⁻¹ᵁ ⊤)).op
    (Scheme.Modules.pullbackLocalSection T (𝔓.σ i))

end INVARSol
end P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_nonempty_pullback_iso_pullback_of_comp_toProj_eq
