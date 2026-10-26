import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_le_monoidalV2

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

namespace ZSCompSol

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem restrictFunctor_map_app {U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : M ⟶ M')
    (W : U.Opens) : ((Scheme.Modules.restrictFunctor i).map f).app W = f.app (i ''ᵁ W) := rfl

theorem restrictSection_comp (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens) :
    restrictSection (s ≫ f) U = ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ (restrictSection s U) := by
  rfl

theorem coeff_comp (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens)
    (φ : M'.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff (s ≫ f) U φ = coeff s U ((Scheme.Modules.restrictFunctor U.ι).map f ≫ φ) := by
  rfl

theorem coeffIdeal_comp_le (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens) :
    coeffIdeal (s ≫ f) U ≤ coeffIdeal s U := by
  apply Ideal.span_mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨(Scheme.Modules.restrictFunctor U.ι).map f ≫ φ, (coeff_comp s f U φ).symm⟩

end ZSCompSol

theorem solution
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) ≤ Scheme.Modules.zeroSchemeIdeal s := by
  apply Scheme.Modules.le_zeroSchemeIdeal
  intro J hJ
  exact Scheme.Modules.zeroSchemeIdeal_le fun U => (ZSCompSol.coeffIdeal_comp_le s f U.1).trans (hJ U)
