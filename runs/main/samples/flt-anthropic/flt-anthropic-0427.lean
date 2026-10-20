namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked_of_dvd

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace Transfer

open IsLocalRing

theorem exists_pow_mul_eq_of_mem_adjoin {C K : Type*} [CommRing C] [Field K] [Algebra C K]
    (J : Ideal C) (t : C) (ht : t ∈ J) (T : Set K)
    (hT : ∀ x ∈ T, ∃ i ∈ J, x * algebraMap C K t = algebraMap C K i)
    {b : K} (hb : b ∈ Algebra.adjoin C T) :
    ∃ N : ℕ, ∃ c ∈ J ^ N, b * algebraMap C K t ^ N = algebraMap C K c := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, hi, hx⟩ := hT x hx
      exact ⟨1, i, by rw [pow_one]; exact hi, by rw [pow_one]; exact hx⟩
  | algebraMap c =>
      exact ⟨0, c, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top, by rw [pow_zero, mul_one]⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      obtain ⟨M, d, hd, hyd⟩ := ihy
      refine ⟨N + M, c * t ^ M + d * t ^ N, ?_, ?_⟩
      · refine Ideal.add_mem _ ?_ ?_
        · rw [pow_add]; exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ht M)
        · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow ht N)
      · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hxc, ← hyd]
        ring
  | mul x y hx hy ihx ihy =>
      obtain ⟨N, c, hc, hxc⟩ := ihx
      obtain ⟨M, d, hd, hyd⟩ := ihy
      refine ⟨N + M, c * d, ?_, ?_⟩
      · rw [pow_add]; exact Ideal.mul_mem_mul hc hd
      · rw [map_mul, ← hxc, ← hyd]
        ring

end Transfer
end P2MW.S_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_away_eq_div_add_sum_of_eq_add_sum_of_drinfeldChartWitness_linked_of_dvd
