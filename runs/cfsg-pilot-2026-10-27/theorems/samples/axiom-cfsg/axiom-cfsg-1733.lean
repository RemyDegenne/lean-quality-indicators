public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G} (c : OI13Ctx L z t T E B β S α σ)

include c

theorem Qs_normalizes_U {y : G} (hy : OYFacts c y) {q : G} (hq : q ∈ c.Qs) :
    ∀ u ∈ Y0 y α ⊔ c.E0 hy, q * u * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy := by
  obtain ⟨hE, hY⟩ := PQ_Qs c hy hq
  have hyY : y ∈ Y0 y α := subset_closure (by simp)
  have hαY : α ∈ Y0 y α := subset_closure (by simp)
  let K : Subgroup G := (Y0 y α ⊔ c.E0 hy).comap (MulAut.conj q).toMonoidHom
  have hK_E : c.E0 hy ≤ K := by
    intro e he
    obtain ⟨e', he', a, ha, eq⟩ := hE e he
    show q * e * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy
    rw [eq]
    exact mul_mem (Subgroup.mem_sup_right he') (Subgroup.mem_sup_left (Zs_le_Y0 c hy ha))
  have hK_Y : Y0 y α ≤ K := by
    unfold Y0
    refine (Subgroup.closure_le K).2 ?_
    intro v hv
    rcases Set.mem_insert_iff.1 hv with hv' | hv'
    · rw [hv']
      obtain ⟨e', he', a, ha, eq⟩ := hY
      show q * y * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy
      rw [eq]
      exact mul_mem (mul_mem (Subgroup.mem_sup_right he')
        (Subgroup.mem_sup_left (Zs_le_Y0 c hy ha))) (Subgroup.mem_sup_left hyY)
    · rw [Set.mem_singleton_iff.1 hv']
      show q * α * q⁻¹ ∈ Y0 y α ⊔ c.E0 hy
      have hc : q * α = α * q := (c.Zs_comm_Qs c.alpha_mem_Zs hq).symm
      have e : q * α * q⁻¹ = α := by
        rw [hc]
        group
      rw [e]
      exact Subgroup.mem_sup_left hαY
  have hU : Y0 y α ⊔ c.E0 hy ≤ K := sup_le hK_Y hK_E
  intro u hu
  exact hU hu

end OI13Ctx
end CFSG.EvenSporadicStandard.Fin76b
end
