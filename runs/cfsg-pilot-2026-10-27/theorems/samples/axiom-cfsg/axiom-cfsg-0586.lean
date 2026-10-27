public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem Q_comm_P {K : Subgroup G} (hII : II4_4_4_center) (hK : K = K₁ ∨ K = K₂) :
    ∀ q ∈ Qof S K, ∀ p ∈ Pof S K, q * p = p * q := by
  have hM := h.m4 hII
  intro q hq p hp
  have h1 : ⁅p, q⁆ ∈ pPrimeCoreOf 2 K := hq.2.2.2 p hp.2
  have h2 : ⁅p, q⁆ ∈ S := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp.1 hq.1) (inv_mem hp.1)) (inv_mem hq.1)
  have h3 : ⁅p, q⁆ ∈ S ⊓ pPrimeCoreOf 2 K := ⟨h2, h1⟩
  rw [M.inf_eq_bot_of_pgroup_odd hM.S_pgroup (hM.core K hK).odd, Subgroup.mem_bot,
    commutatorElement_def] at h3
  have h4 : p * q = q * p := by
    have h5 : p * q * p⁻¹ * q⁻¹ = 1 := h3
    calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
      _ = q * p := by rw [h5, one_mul]
  exact h4.symm

end Cfg65
end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
end
