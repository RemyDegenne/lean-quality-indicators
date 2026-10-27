public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup

variable {H : Type*} [Group H] [Finite H] {S : Subgroup H} {x : H}

theorem Hyp3.card_Q (h : Hyp3 H S x) : Nat.card (oQ H) = 4 * Nat.card (q0Sub H x) := by
  have : (q0Sub H x).Normal := h.q0_normal
  have hdisj : nQ H x ⊓ q0Sub H x = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro n ⟨hn, hq⟩
    exact h.nQ_inf_q0 hn hq
  have hsup : nQ H x ⊔ q0Sub H x = oQ H := by
    refine le_antisymm (sup_le ((nQ_le x).trans oneCenter_le) q0Sub_le_Q) ?_
    intro q hq
    obtain ⟨n, hn, q₀, hq₀, rfl⟩ := h.decomp hq
    exact Subgroup.mul_mem_sup hn hq₀
  have h1 := card_sup_of_inf_eq_bot (nQ H x) (q0Sub H x) hdisj
  rw [hsup, h.offender.1] at h1
  exact h1

end CFSG.Quasithin.Fan86.Sigma3
end
