namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion

set_option autoImplicit false

universe u v

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

namespace GlueHom

p2m_open

p2m_open

section Glue

variable {X Y₀ Y₁ Y₀₁ : Scheme.{u}} (f₀ : Y₀ ⟶ X) (f₁ : Y₁ ⟶ X) [IsOpenImmersion f₀] [IsOpenImmersion f₁]
  (g₀ : Y₀₁ ⟶ Y₀) (g₁ : Y₀₁ ⟶ Y₁) [IsOpenImmersion g₀] [IsOpenImmersion g₁]
  (hg : g₀ ≫ f₀ = g₁ ≫ f₁)

variable (hov : f₀.opensRange ⊓ f₁.opensRange ≤ (g₀ ≫ f₀).opensRange)

variable (N : X.Modules)

theorem η_comm : η₀ f₀ N ≫ a f₀ g₀ N = η₁ f₁ N ≫ b f₀ f₁ g₀ g₁ hg N := by
  apply Scheme.Modules.hom_ext; intro W; ext s
  rw [comp_app_apply, comp_app_apply, a_apply, b_apply, η₀_apply, η₁_apply, map_map, map_map]
  rfl

end Glue
end GlueHom
end Modules
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_restrict_eq_of_isOpenImmersion
