public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS

variable {G : Type} [Group G] {t z : G} {S Eg T T' W0 : Subgroup G}

theorem HarCoreData.conj_t_eq (D : HarCoreData t z S Eg T T' W0) {n : G}
    (hn : n ∈ normalizer (S : Set G)) (hnt : n * t * n⁻¹ ≠ t) : n * t * n⁻¹ = t * z := by
  have htS : t ∈ S := HarCoreData.T_le_S D D.t_mem
  have htc : ∀ s ∈ S, s * t = t * s := fun s hs => D.S_comm_t s hs
  have hnT' : n ∈ normalizer (T' : Set G) := HarCoreData.normalizer_T' D hn
  rcases HarCoreData.conj_mem_V D hn htS htc with h | h | h | h
  · exfalso
    apply D.t_ne_one
    calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · exact absurd h hnt
  · exfalso
    have h1 := harSqCard_conj T' hnT' t
    rw [h, D.card_T0'_z1, D.card_T0'_t] at h1
    omega
  · exact h

end CFSG.EvenSporadicStandard.HNRecog.Harada
end
