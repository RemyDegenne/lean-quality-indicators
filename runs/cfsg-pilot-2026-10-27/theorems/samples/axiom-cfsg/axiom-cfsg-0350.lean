public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4

open scoped commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

namespace U4qBase

theorem isOmega4MinusType_L1 (B : X.U4qBase) :
    CFSG.Quasithin.IsOmega4MinusType (X.L 1) (X.n 0) := by
  haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (X.L_le_Gi 1)
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hn := n1_eq_two_mul B
  have hT : IsSylowTwoOf X.S (X.L 1) := by
    simpa [X.edgeSylow_zero] using X.isSylowTwoOf_edgeSylow_L_succ 0
  obtain ⟨t, ht, t', ht', u, hu, hne⟩ := not_quadratic_Q1 B
  have hq := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
  rw [show nOf Γ (X.vert 1) = 2 * X.n 0 from hn] at hq
  refine CFSG.Quasithin.F112R.St84.isOmega4MinusType_of_irreducible_of_not_quadratic
    (by have := B.gen.hyp.two_le_n 0; omega) hq ?_ ?_ ?_ ?_ hT ?_ <;> rw [hQ1]
  · exact B.elem_Q1
  · rw [B.card_Q1, hn]
    congr 1
    omega
  · exact B.Q1_irred hn
  · intro hL
    have hc : ⁅t', u⁆ = 1 := by
      have hcomm := Subgroup.mem_centralizer_iff.mp (hL (hT.1 ht')) u hu
      rw [commutatorElement_def, ← hcomm]
      group
    exact hne (by rw [hc, commutatorElement_one_right])
  · exact ⟨t, ht, t', ht', u, hu, hne⟩

end U4qBase
end Setup
end CFSG.Quasithin.St84
end
