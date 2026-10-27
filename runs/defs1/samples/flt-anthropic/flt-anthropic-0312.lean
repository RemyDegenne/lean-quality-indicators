set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {k : Type u} [Field k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))

variable {a}

section

variable [IsSeparated a]

abbrev constDiv (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) : RelEffCartierDiv a 1 a :=
  RelEffCartierDiv.ofPoint a (a ≫ ε.1) (comp_point_comp ε)

end
end AlgebraicGeometry.RelPicard
end
