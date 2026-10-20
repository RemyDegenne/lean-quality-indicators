set_option autoImplicit false

open CategoryTheory

namespace Rep

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G] (Λ : Subgroup G) [Λ.Normal]

theorem quotientRightTranslation_one : quotientRightTranslation (k := k) Λ 1 = 𝟙 _ := by
  apply Rep.hom_ext; refine DFunLike.ext _ _ fun x => ?_
  show Finsupp.mapDomain (· * (1 : G ⧸ Λ)⁻¹) x = x
  simp only [inv_one, mul_one]
  exact Finsupp.mapDomain_id

end Rep
