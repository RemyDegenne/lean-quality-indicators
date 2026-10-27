public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

section CenterPrime

variable {n d : ℕ} {F : Type} [Field F] [Finite F]

theorem ggCenterPrime_psu_even
    (hF : Nat.card F = (2 ^ n) ^ 2) {p : ℕ}
    (hd : Even d) (hd4 : 4 ≤ d) (hq : 4 ≤ 2 ^ n) (hpq : ¬ p ∣ 2 ^ n + 1) :
    GGCenterPrime p (StatedProj (StatedSU d (2 ^ n) F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  intro L' _ _ ψ hψ hker hperf hpZ
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_of_sections
    (QuotientGroup.mk' ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hF hd hd4 hq
        hπ hcen)
    ψ hψ hker hperf
  have hZker : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center (StatedProj (StatedSU d (2 ^ n) F)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [center_statedProj_statedSU_eq_bot hF hd4, Subgroup.mem_bot] at hzc
    exact hzc
  have hkerMap : ψ.ker ≤
      ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)).map φ := by
    intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    rw [MonoidHom.mem_ker, hφ g] at hl
    exact Subgroup.mem_map.mpr ⟨g, (QuotientGroup.eq_one_iff g).mp hl, rfl⟩
  have hdvd : Nat.card (Subgroup.center L') ∣ 2 ^ n + 1 :=
    ((Subgroup.card_dvd_of_le (hZker.trans hkerMap)).trans
      (Subgroup.card_map_dvd
        (H := (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)) φ)).trans
      (card_scalars_statedSU_dvd hF (by omega))
  exact hpq (dvd_trans hpZ hdvd)

end CenterPrime
end CFSG.StandardType
end
