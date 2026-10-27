namespace P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical

p2m_open

namespace NeronLeg1TwoBranches

section Transport

variable {L : Type*} [Field L] (A : ValuationSubring L)

variable {F : Type*} [Field F] [Algebra L F]

variable {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]

def transport (R : RegularProlongation A F Fb) (w : F ≃ₐ[L] F) : RegularProlongation A F Fb where
  integers := R.integers.comap (w : F →+* F)
  residue := R.residue.comp (comapHom A R w)
  algebraMap_mem_iff x := by
    rw [mem_comap_iff, AlgEquiv.commutes]
    exact R.algebraMap_mem_iff x
  residue_surjective z := by
    obtain ⟨f, hf⟩ := R.residue_surjective z
    exact ⟨symmHom A R w f, by rw [RingHom.comp_apply, comapHom_symmHom, hf]⟩
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R.ker_residue,
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, not_iff_not]
    constructor
    · intro hu; simpa [symmHom_comapHom] using hu.map (symmHom A R w)
    · intro hu; exact hu.map (comapHom A R w)
  residue_algebraMap a := by
    rw [RingHom.comp_apply]
    convert R.residue_algebraMap a using 2
    exact Subtype.ext (by simp)
  exists_smul_mem f hf := by
    have hwf : w f ≠ 0 := (map_ne_zero_iff _ w.injective).mpr hf
    obtain ⟨c, hc, hne⟩ := R.exists_smul_mem (w f) hwf
    have hmem : c • f ∈ R.integers.comap (w : F →+* F) := by
      rw [mem_comap_iff, map_smul]; exact hc
    refine ⟨c, hmem, ?_⟩
    rw [RingHom.comp_apply]
    have h : comapHom A R w ⟨c • f, hmem⟩ = ⟨c • w f, hc⟩ := Subtype.ext (by simp)
    rwa [h]

end Transport
end NeronLeg1TwoBranches
end
end P2MW.S_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
