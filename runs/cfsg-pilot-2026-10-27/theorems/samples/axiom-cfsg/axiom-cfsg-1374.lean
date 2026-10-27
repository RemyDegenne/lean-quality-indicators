public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42

open Equiv Subgroup AltStdCycTwo AltStdBal MulAction

section Config

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin 9)}
  {z : G}

theorem vElt_injective (c : Config G L Q 9 θ z) : Function.Injective (vElt θ z) := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have hzL := z_not_mem_L c
  cases a <;> cases b
  · rw [vElt_false, vElt_false] at h
    rw [bG_injective θ h]
  · rw [vElt_false, vElt_true] at h
    exfalso
    apply hzL
    have h1 : z = (bG θ l)⁻¹ * bG θ k := by rw [h]; group
    rw [h1]
    exact mul_mem (inv_mem (bG_mem θ l)) (bG_mem θ k)
  · rw [vElt_true, vElt_false] at h
    exfalso
    apply hzL
    have h1 : z = (bG θ k)⁻¹ * bG θ l := by rw [← h]; group
    rw [h1]
    exact mul_mem (inv_mem (bG_mem θ k)) (bG_mem θ l)
  · rw [vElt_true, vElt_true] at h
    rw [bG_injective θ (mul_right_cancel h)]

end Config
end CFSG.OddStandard.AltStdSmall4.Fus.P42
end
