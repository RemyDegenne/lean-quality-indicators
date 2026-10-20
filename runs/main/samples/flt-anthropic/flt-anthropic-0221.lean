namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing

set_option autoImplicit false

universe u

p2m_open

noncomputable section

namespace F6ea14e94

open Opposite DirectSum

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)

scoped instance (n : ℕ) : AddCommGroup (Sec f L n) := inferInstanceAs (AddCommGroup Γ(L.tensorPow n, ⊤))

scoped instance (n : ℕ) : Module Γ(X, ⊤) (Sec f L n) := inferInstanceAs (Module Γ(X, ⊤) Γ(L.tensorPow n, ⊤))

scoped instance (n : ℕ) : Module S (Sec f L n) := Module.compHom (Sec f L n) (baseHom f)

scoped instance : GradedMonoid.GMul (Sec f L) where
  mul a b := mulSec f L a b

scoped instance : GradedMonoid.GOne (Sec f L) where
  one := (unitSection ⊤ : Γ(𝟙_ X.Modules, ⊤))

scoped instance : DirectSum.GNonUnitalNonAssocSemiring (Sec f L) where
  mul_zero a := by
    rw [gmul_def]
    erw [tensorSections_zero_right]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_zero
  zero_mul b := by
    rw [gmul_def]
    erw [tensorSections_zero_left]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_zero
  mul_add a b c := by
    rw [gmul_def, gmul_def, gmul_def]
    erw [tensorSections_add_right]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_add _ _
  add_mul a b c := by
    rw [gmul_def, gmul_def, gmul_def]
    erw [tensorSections_add_left]
    exact ((tensorPowAdd L _ _).hom.app ⊤).hom.map_add _ _

section Frames

variable [Fact (Scheme.Modules.IsInvertible L)]

theorem isFrameOn_frG (x : X) : IsFrameOn (frG L x) (frU L x) :=
  (IsInvertible.exists_isFrameOn_monoidalV2 (Fact.out : Scheme.Modules.IsInvertible L) x).choose_spec.choose_spec.2

end Frames
end F6ea14e94
end
end P2MW.S_AlgebraicGeometry_GradedOAlgebra_exists_isSectionRing
