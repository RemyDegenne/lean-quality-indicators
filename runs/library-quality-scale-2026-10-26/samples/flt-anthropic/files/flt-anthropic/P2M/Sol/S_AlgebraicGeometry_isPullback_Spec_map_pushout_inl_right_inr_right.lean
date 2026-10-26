import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isPullback_Spec_map_pushout_inl_right_inr_right

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] {B B₁ B₂ : Under (CommRingCat.of R)} (φ₁ : B ⟶ B₁) (φ₂ : B ⟶ B₂) :
    IsPullback (Spec.map (pushout.inl φ₁ φ₂).right) (Spec.map (pushout.inr φ₁ φ₂).right)
      (Spec.map φ₁.right) (Spec.map φ₂.right) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ ((IsPushout.of_hasPushout φ₁ φ₂).map (Under.forget _))
