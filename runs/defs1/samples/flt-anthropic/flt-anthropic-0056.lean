namespace P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback

set_option autoImplicit false

open scoped Quaternion

p2m_open

noncomputable section

namespace P2mKcQmBcSol

section Square

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
  {S S' : Type} [CommRing S] [CommRing S'] {φ : S →+* S'}
  {X : PolarisedAbelianScheme 2 d m S} {X' : PolarisedAbelianScheme 2 d m S'}
  {gA : X'.A ⟶ X.A}

def SqHom (hg : IsPullback gA X'.f X.f (Spec.map (CommRingCat.ofHom φ))) : Prop :=
  ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' X'.f),
    (X'.L.mul t' x y).1 ≫ gA = (X.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ)) (gPt hg x) (gPt hg y)).1

end Square
end P2mKcQmBcSol
end
end P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_isPullback
