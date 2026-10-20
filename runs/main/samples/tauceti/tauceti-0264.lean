public section

open ComplexConjugate Filter

open scoped ComplexOrder Topology

namespace TauCeti

variable {G : Type*} [AddCommGroup G] {F H : G → ℂ}

namespace IsPositiveDefiniteSub

theorem of_posSemidef (hK : Matrix.PosSemidef fun a b : G => F (a - b)) :
    IsPositiveDefiniteSub F := by
  refine isPositiveDefiniteSub_iff_isPositiveDefinite.mpr
    (IsPositiveDefinite.of_posSemidef ?_)
  have h := hK.submatrix fun a : WithNegStar G => WithNegStar.ofNegStar a
  have heq : Matrix.submatrix (Matrix.of fun a b : G => F (a - b))
      (fun a : WithNegStar G => WithNegStar.ofNegStar a)
      (fun a : WithNegStar G => WithNegStar.ofNegStar a) =
      fun a b : WithNegStar G => F (WithNegStar.ofNegStar (a + star b)) := by
    ext a b
    simp [sub_eq_add_neg]
  exact heq ▸ h

end IsPositiveDefiniteSub
end TauCeti
end
