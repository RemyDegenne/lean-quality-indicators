namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections

set_option autoImplicit false

set_option maxHeartbeats 1600000

universe u v

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

p2m_open

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  simp [τ, pullbackCongr]

end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
