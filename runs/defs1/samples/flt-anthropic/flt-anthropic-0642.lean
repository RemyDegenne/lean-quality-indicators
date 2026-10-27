namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

p2m_open

open scoped DirectSum

universe u

namespace AlgebraicGeometry

p2m_open

namespace OModulePresheaf

p2m_open

namespace CechRing

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)

def B : ∀ n : ℕ, Submodule R (Z π K n)
  | 0 => ⊥
  | n + 1 => (LinearMap.range ((unit π).d K n)).comap (Z π K (n + 1)).subtype

end CechRing
end OModulePresheaf
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit
