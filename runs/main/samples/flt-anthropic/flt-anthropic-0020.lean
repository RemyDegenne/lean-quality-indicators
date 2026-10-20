namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul

set_option autoImplicit false

universe u

p2m_open

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

p2m_open

variable {X Y : Scheme.{u}}

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "app_smul mapPresheaf app" end Hom

p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

@[reassoc] lemma smulHom_comp (s : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    smulHom s M ≫ φ = φ ≫ smulHom s N := by
  ext U x
  change φ.app U ((smulHom s M).app U x) = (smulHom s N).app U (φ.app U x)
  rw [smulHom_app_apply, smulHom_app_apply, Hom.app_smul]

end Hom
end Modules
end Scheme
end AlgebraicGeometry
end P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul
