namespace P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift

set_option autoImplicit false

universe u

p2m_open

namespace KummerLift

variable {X : Scheme.{u}} [IsIntegral X]

section KummerAlgebra

variable (k : ℕ) (g : X.functionField)

noncomputable abbrev fK : Spec (CommRingCat.of (KA k g)) ⟶ X :=
  Spec.map (φK k g) ≫ X.fromSpecStalk (genericPoint X)

end KummerAlgebra
end KummerLift
end P2MW.S_AlgebraicGeometry_exists_root_fromNormalization_kummer_existsUnique_lift
