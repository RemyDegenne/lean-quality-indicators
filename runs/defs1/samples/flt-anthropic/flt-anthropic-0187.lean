namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq

set_option autoImplicit false

p2m_open

universe u

namespace PV1TL

p2m_open

variable {Y : Scheme.{u}}

variable {𝒱 : Y.OrderedAffineCover} {𝓜 : Y.Modules} (τ : CechTrivialisation 𝒱 𝓜)

noncomputable def κiso (𝓜 : Y.Modules) {W W' : Y.Opens} (h' : W' ≤ W) :
    (Scheme.Modules.pullback (Y.homOfLE h')).obj ((Scheme.Modules.pullback W.ι).obj 𝓜) ≅
      (Scheme.Modules.pullback W'.ι).obj 𝓜 :=
  (pullbackComp (Y.homOfLE h') W.ι).app 𝓜 ≪≫ (pullbackCongr (Y.homOfLE_ι h')).app 𝓜

end PV1TL
end P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_refinement_transition_eq
