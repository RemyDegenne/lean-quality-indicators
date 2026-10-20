namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace BiAffine29

variable {𝒪 : Type} [CommRing 𝒪]

section Ev

variable {X T : Scheme.{0}} [IsAffine T] (f : X ⟶ Spec (CommRingCat.of 𝒪)) (t : T ⟶ Spec (CommRingCat.of 𝒪))
  {ϖ : Γ(X, ⊤)} (d : ∀ n : ℕ, Γ(T, ⊤) →+* Γ(X, ⊤) ⧸ Ideal.span {ϖ ^ n})

theorem kill_mono (ϖ : Γ(X, ⊤)) {B : Type} [CommRing B] (η : Γ(X, ⊤) →+* B) (N j : ℕ)
    (hN : ∀ a ∈ Ideal.span {ϖ ^ N}, η a = 0) : ∀ a ∈ Ideal.span {ϖ ^ (N + j)}, η a = 0 :=
  fun a ha => hN a (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_add_right N j)) ha)

end Ev
end BiAffine29
end P2MW.S_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isAffine_of_isAffine_of_isNoetherianRing
