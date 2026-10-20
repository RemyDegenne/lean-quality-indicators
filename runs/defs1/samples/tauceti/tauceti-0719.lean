public section

noncomputable section

open Set Metric Complex

namespace TauCeti

namespace ThricePuncturedSphere

/-- **The fundamental group of `A = {re z < 1}` is infinite cyclic**: `π₁(A, 1/2) ≃* ℤ`. It is the
punctured star-convex computation for the half-plane `re z < 1` punctured at `0`, and it sends the
class of `γ0` to `1` (`leftOpenFundamentalGroupMulEquivInt_periph0Left`). -/
def leftOpenFundamentalGroupMulEquivInt :
    FundamentalGroup leftOpen ⟨basePt, basePt_mem_leftOpen⟩ ≃* Multiplicative ℤ :=
  (FundamentalGroup.homeomorphMulEquivOfEq leftOpenHomeomorph leftOpenHomeomorph_basePt).trans
    (starConvex_halfPlane.fundamentalGroupMulEquivInt one_half_pos sphere_subset_halfPlane _)

end ThricePuncturedSphere
end TauCeti
end
end
