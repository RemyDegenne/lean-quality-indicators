public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open scoped commutatorElement

namespace ThmE

section Sev1

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.center_eq_bot (h6 : E18_6 r) (c : MinCex r Ω K S R W H) :
    Subgroup.center G = ⊥ := by
  obtain ⟨-, F, -, -, -, hF⟩ := h6 G Ω K S R W H c
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp hx y)
  rw [hF] at this
  exact this

end Sev1
end ThmE
end CFSG.CGT.PushingUpLit.SolKNA.R4
end
