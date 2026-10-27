public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)

include h

theorem le_commutator_sup_ch616 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2)
    (h614 : Stmt6_1_4) (h615 : Stmt6_1_5) (h626 : Stmt6_2_6) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) (hlt : ch6ZS T L V < V ⊓ uCh611 T L V) :
    V ⊓ uCh611 T L V ≤ ⁅V, uCh611 T L V⁆ ⊔ zCh611 T := by
  obtain ⟨v, hv, hvU⟩ := h.exists_not_mem_U_ch615 h6210 h6211 h6212 hlt
  intro x hx
  obtain ⟨a, ha, haz⟩ :=
    h.exists_comm_eq_U_ch616 h331 h432 h512 h614 h615 h626 h6210 h6211 h6212 hlt hv hvU x hx
  have e : x = ⁅v, a⁆ * (⁅v, a⁆⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hv ha))
    (Subgroup.mem_sup_right haz)

end Hyp6Sec2
end CFSG.Quasithin.H13
end
