public section

open MulAction

namespace CategoryTheory.ActionCategory

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

section FixedPoints

variable (G) in
/-- At a fixed point of the action, the isotropy group is all of `G`, including every element
acting trivially on `X`. -/
def autMulEquivOfMemFixedPoints {x : X} (hx : x ∈ fixedPoints G X) :
    Aut (objEquiv G X x) ≃* G :=
  (stabilizerMulEquivAut G x).symm.trans
    ((MulEquiv.subgroupCongr ((Subgroup.eq_top_iff' _).2 fun g => hx g)).trans Subgroup.topEquiv)

end FixedPoints
end CategoryTheory.ActionCategory
end
