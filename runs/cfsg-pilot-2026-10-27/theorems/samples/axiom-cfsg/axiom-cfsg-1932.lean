public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem existsCommSpec_of_oneOppositeClosed (hD : IsRootInvolutionSet D)
    (hconn : Moufang.ExcCollConnected D) (hK : OneOppositeClosed D) : ExistsCommSpec D := by
  intro d hd c hc hdc hodd
  obtain ⟨e, he, hce, -, h4⟩ := oneOpposite_of_collConnected hD hconn hK hc hd
    (fun h => hdc h.symm) (by rw [orderOf_mul_comm_eq]; exact hodd)
  exact ⟨e, he, hce.symm, h4⟩

end CFSG.Timmesfeld.Bridge
end
