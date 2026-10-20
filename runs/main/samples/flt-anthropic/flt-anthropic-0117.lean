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

theorem toPt_map_zero (v : TangentPoints x (unitPt L) V) :
    toPt L (v.map (0 : V →ₗ[K] W)) = L.one (SquareZero.toBase K W) := by
  apply Subtype.ext
  rw [toPt_coe, TangentPoints.map_coe, specMap_zero, Category.assoc, v.2.2, one_toBase_coe]

end GroupLaw
end D2aTandim
end
end P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_finrank_eq_two_of_range_iff_isTangentVector
