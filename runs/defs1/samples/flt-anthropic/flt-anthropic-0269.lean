namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal

set_option autoImplicit false

universe u

p2m_open

noncomputable section

namespace ZeroSchemeBC

p2m_open

variable {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M)

def triv {U : X.Opens} (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {Ω : X'.Opens}
    (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback F).obj M).restrict Ω.ι ≅ 𝟙_ (Ω : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback Ω.ι).app _ ≪≫
  (pullbackComp Ω.ι F).app M ≪≫
  (pullbackCongr (G_comp F hΩ).symm).app M ≪≫
  ((pullbackComp (F.resLE U Ω hΩ) U.ι).app M).symm ≪≫
  (Scheme.Modules.pullback (F.resLE U Ω hΩ)).mapIso
    (((restrictFunctorIsoPullback U.ι).app M).symm ≪≫ τ) ≪≫
  Scheme.Modules.pullbackUnitIso (F.resLE U Ω hΩ)

end ZeroSchemeBC
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
