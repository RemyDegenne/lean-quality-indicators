public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.GLTheoremA

section Equivalence

theorem ggTwE6OddLayerCores_iff_centre :
    GGTwE6OddLayerCores ↔ GGTwE6OddLayerCentre := by
  constructor
  · intro h f hf A hA hAc hAD z hz hzc hz2
    obtain ⟨β, T, hT⟩ := h f hf A hA hAc hAD
    exact LayerCores.layerCentre_of_isSubCoreFamily hT z hz hzc hz2
  · intro h f hf A hA hAc hAD
    haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
      Subtype.finite
    have hq := TwE6Nonsplit.isQuasisimple_graphFixedRootGroup f hf
    have hZ0 : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) = ⊥ :=
      CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.center_graphFixedRootGroup_E6_eq_bot
        (frobQ 2 f)
    let eZ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≃*
        (↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⧸
          Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
            (frobQ 2 f))) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ0).trans QuotientGroup.quotientBot).symm
    haveI := hq.2.1
    haveI hS : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) := eZ.isSimpleGroup
    have hnc : ∃ a b : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
    have hEq : LayerSixE.autFix A = I142.centFix A :=
      Subgroup.ext fun x => LayerSixE.mem_autFix.trans I142.mem_centFix.symm
    have key := (LayerCores.exists_subCoreFamily_iff_layerCentre_odd hS hnc
      (TwE6LayerRest.isChevSimple_graphFixedRootGroup f hf) A hA hAc).2
      (by rw [← hEq]; exact h f hf A hA hAc hAD)
    rw [← hEq] at key
    exact key

end Equivalence
end CFSG.StandardType
end
