set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

attribute [instance] Scheme.OrderedAffineCover.instFintype Scheme.OrderedAffineCover.instLinearOrder

attribute [instance] OModulePresheaf.addCommGroup OModulePresheaf.module OModulePresheaf.moduleSections
  OModulePresheaf.isScalarTower

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

abbrev HSucc (i : ℕ) : Type u :=
  LinearMap.ker (F.d K (i + 1)) ⧸ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype

end OModulePresheaf
end AlgebraicGeometry
end
