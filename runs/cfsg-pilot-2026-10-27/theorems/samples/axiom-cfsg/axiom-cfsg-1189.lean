public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.LieType.ChevTwo.OppCl.U33Fin
  CFSG.LieType.BorelTits CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

section Model

variable {K : Type} [Group K]
  (e : K ≃* QP.originalSubgroup)

theorem zk_central {x : K} (hx : x ∈ Tk e) (hxc : ∀ y ∈ Tk e, x * y = y * x) :
    x ∈ Subgroup.zpowers (zk e) := by
  refine mem_zpowers_zk_of_mem_zL e (Z_facts.2.2.2.2 _ ((mem_Tk e).1 hx) fun y' hy' => ?_)
  obtain ⟨y, hy⟩ := psi_surj e (T0L_facts.2.2.2.2.1 y' hy')
  have hyT : y ∈ Tk e := by rw [mem_Tk, hy]; exact hy'
  rw [← hy, ← map_mul, ← map_mul, hxc y hyT]

end Model
end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin
end
