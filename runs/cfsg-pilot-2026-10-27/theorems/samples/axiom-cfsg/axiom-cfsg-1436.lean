public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits

open scoped commutatorElement Pointwise

namespace L14333

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4

open CFSG.Quasithin.H13.L14333.Ctx_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx_F4 G T L V V₂ K g a z b d x D)

include c

theorem zU_le_pCoreOf_F4 : centerOf (fsuU T V) ≤ pCoreOf 2 (L ⊔ T) := by
  refine le_trans ?_ c.cent_le_pCoreOf_F4
  intro y hy
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (c.U_le_T_F4 (Subgroup.mem_inf.mp hy).1),
    Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 v (c.ctx.V_U hv)

end Ctx_F4
end L14333
end CFSG.Quasithin.H13
end
