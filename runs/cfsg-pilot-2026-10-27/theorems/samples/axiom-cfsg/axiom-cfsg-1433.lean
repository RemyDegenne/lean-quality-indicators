public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

universe u

variable {G : Type u} [Group G]

theorem point_centralizer_index_of_full_offBase_orbit (H A : Subgroup G)
    (hAH : A ≤ H) (u : G) (huH : u ∈ H)
    (hAC : A ≤ Subgroup.centralizer ({u} : Set G))
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hbetafix : pointRightCosetMul H beta u = beta)
    (horbit : ∀ omega ∈ cosetFixedSet H u, omega ≠ rightCosetMk H 1 →
      ∃ a : A, pointRightCosetMul H beta (a : G) = omega) :
    (pairPointStabilizer H beta).relIndex A = Nat.card (cosetFixedSet H u) - 1 := by
  let := pointSubgroupInverseRightAction H A
  have hset : MulAction.orbit A beta = cosetFixedSet H u \ {rightCosetMk H 1} := by
    ext omega
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, rfl⟩
      change pointRightCosetMul H beta (a : G)⁻¹ ∈ cosetFixedSet H u ∧
        pointRightCosetMul H beta (a : G)⁻¹ ∉ ({rightCosetMk H 1} : Set _)
      exact ⟨point_centralizer_preserves_cosetFixedSet H u _
          (hAC (A.inv_mem a.property)) hbetafix,
        point_subgroup_preserves_nonbase H _ (hAH (A.inv_mem a.property)) hbeta⟩
    · rintro ⟨hfix, hnonbase⟩
      obtain ⟨a, ha⟩ := horbit omega hfix hnonbase
      refine ⟨a⁻¹, ?_⟩
      change pointRightCosetMul H beta ((a⁻¹ : A) : G)⁻¹ = omega
      simpa only [Subgroup.coe_inv, inv_inv] using ha
  have hbase : rightCosetMk H 1 ∈ cosetFixedSet H u :=
    (point_right_base_fixed_iff H u).mpr huH
  calc
    _ = (MulAction.stabilizer A beta).index := by
      rw [point_subgroup_stabilizer_eq_pair H A hAH beta]
      rfl
    _ = (MulAction.orbit A beta).ncard := MulAction.index_stabilizer A beta
    _ = (cosetFixedSet H u).ncard - 1 := by
      rw [hset, Set.ncard_sdiff_singleton_of_mem hbase]
    _ = Nat.card (cosetFixedSet H u) - 1 := by rw [Nat.card_coe_set_eq]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
end
