namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Quaternion

universe u

namespace D2aTandim

section GroupLaw

variable {K : Type u} [Field K] {X : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of K)}

variable (L : RelativeGroupLaw K x)

variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

variable {W : Type u} [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

variable {W' : Type u} [AddCommGroup W'] [Module K W'] [Module Kᵐᵒᵖ W'] [IsCentralScalar K W']

theorem comp_basePoint_toPt (v : TangentPoints x (unitPt L) V) :
    schemeHomOverComp (SquareZero.basePoint K V) (SquareZero.basePoint_toBase K V) (toPt L v) = L.one (𝟙 _) :=
  Subtype.ext v.2.2

end GroupLaw
end D2aTandim
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector
