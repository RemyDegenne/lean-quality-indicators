public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup

section Twist

variable {G M : Type*} [Group G] [Group M]

theorem QCover.TwistOn.mono {c c' : QCover G M} {Q Q' : Subgroup G} {ε : M →* M}
    (h : c.TwistOn c' Q ε) (hQQ : Q' ≤ Q) : c.TwistOn c' Q' ε := by
  obtain ⟨hQ, hQ', h⟩ := h
  exact ⟨hQQ.trans hQ, hQQ.trans hQ', fun y hy => h y (hQQ hy)⟩

end Twist
end CFSG.SeitzReduction.TwistedE6Pilot
end
