namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_of_isAffineOpen

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace W2L15

section YSide

variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
  {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
  {xt : ∀ n : ℕ, X n ⟶ X (n + 1)} {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
  (D : TowerQuotientDatum 𝒪 π X xb xt G a)
  (V : ∀ n : ℕ, (D.Y n).Opens) (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)

theorem ρY_ker (hVa : ∀ n : ℕ, IsAffineOpen (V n)) (m : ℕ) (y : Γ(D.Y (m + 1), V (m + 1))) (hy : ρY D V hV m y = 0) :
    ∃ z : Γ(D.Y (m + 1), V (m + 1)), y = (sY D V (m + 1) π) ^ (m + 1) * z :=
  ((level_surjective_and_ker 𝒪 π m (D.Y m) (D.Y (m + 1)) (D.yb m) (D.yb (m + 1)) (D.yt m) (D.yt_isPullback m)
    (V m) (hVa m) (V (m + 1)) (hVa (m + 1)) (hV m) (by rw [hV])).2 y).1 hy

end YSide
end W2L15
end P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_of_isAffineOpen
