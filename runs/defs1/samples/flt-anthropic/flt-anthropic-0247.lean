namespace P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed

open WeierstrassCurve

namespace P2MKcCQJbc

variable {A B : Type*} [Field A] [Field B] [DecidableEq A] [DecidableEq B] (f : A →+* B)

noncomputable def ptMap (V : WeierstrassCurve A) : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI : Algebra A B := f.toAlgebra
  (WeierstrassCurve.Affine.Point.map (W' := V) (Algebra.ofId A B) :
    (V.baseChange A).toAffine.Point →+ (V.baseChange B).toAffine.Point)

end P2MKcCQJbc
end P2MW.S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
