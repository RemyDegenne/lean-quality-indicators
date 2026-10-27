public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open scoped MatrixGroups

section Model

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem tightCore_eq_self_of_twoGroup_quot (hΦ : HypOmegaGen Φ)
    (h2 : ∀ J ∈ Φ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)) :
    ∀ K ∈ Φ, tightCore K = K := by
  intro K hK
  rcases hΦ.omega2 K hK with h | h
  · exact h
  · obtain ⟨e⟩ := h
    exact absurd ((h2 K hK).of_equiv e) not_isPGroup_two_sl2_threeR

end Model
end CFSG.CGT.PushingUpLit.SolKNA.R4
end
