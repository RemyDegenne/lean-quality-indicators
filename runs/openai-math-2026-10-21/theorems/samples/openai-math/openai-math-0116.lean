namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem fixedTop_old_glb {P r μ x y z : ZFSet.{u}} (old : MeetOrderCode P r μ)
    (entry : ZFSet.pair (ZFSet.pair x y) z ∈ μ) :
    GreatestLowerBoundCode (fixedTopCarrier P) (fixedTopOrder P r) x y z := by
  obtain ⟨hx, hy, hz, glb⟩ := old.pair_iff.1 entry
  refine ⟨(fixedTopOrder_old_iff hx).2 glb.1, (fixedTopOrder_old_iff hy).2 glb.2.1, ?_⟩
  intro w _ wx wy
  have hw := fixedTopOrder_no_new_below old.order hx wx
  exact (fixedTopOrder_old_iff hz).2 (glb.2.2 w hw
    ((fixedTopOrder_old_iff hx).1 wx) ((fixedTopOrder_old_iff hy).1 wy))

end PartitionPilot.Forcing
end OAI
