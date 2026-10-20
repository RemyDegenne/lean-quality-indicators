@[expose] public section

namespace UnrestrictedBooleanMul

namespace N4

noncomputable section

theorem NormalizedEight.cubicLowLowNormalCollisionAt
    {C : Circuit 8 8} (h : NormalizedEight C)
    {child low target : ANF 8}
    (hchild : IsLowLowProduct child) (hlow : low ∈ rationalLowSpace)
    (htarget : target ∈ targetAmbient 8 (mulTarget 4))
    (htargetNotLow : target ∉ rationalLowSpace)
    (htargetEq : target = (low + C.gate 3) + child) :
    ∃ (targetAffine : ANF 8) (targetCoeff : TargetCoeff),
      CubicLowLowNormalCollisionAt (C.gate 3) target targetAffine targetCoeff := by
  rcases hchild with ⟨childLeft, childRight,
    hchildLeft, hchildRight, hchildEq⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hchildLeft with
    ⟨childLeftConst, childLeftLinear, childLeftCoeff, hchildLeftRep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hchildRight with
    ⟨childRightConst, childRightLinear, childRightCoeff, hchildRightRep⟩
  rcases exists_targetAmbient_rep htarget with
    ⟨targetAffine, targetCoeff, htargetAffine, htargetRep⟩
  have hchildRep : child =
      (affineANF childLeftConst childLeftLinear +
          rationalANF childLeftCoeff) *
        (affineANF childRightConst childRightLinear +
          rationalANF childRightCoeff) := by
    rw [hchildEq, hchildLeftRep, hchildRightRep]
  have htargetQuartic := quarticProbeANF_eq_zero_of_mem_targetAmbient htarget
  have hlowQuartic := quarticProbeANF_eq_zero_of_mem_targetAmbient
    (rationalLowSpace_le_targetAmbient hlow)
  have hgQuartic := h.seed_quarticProbe_eq_zero
  have hchildQuartic : quarticProbeANF child = 0 := by
    have heq := congrArg quarticProbeANF htargetEq
    rw [map_add, map_add, hlowQuartic, hgQuartic, htargetQuartic] at heq
    simpa using heq.symm
  have hchildProbe : quarticWedgeProbe (rationalTwo childLeftCoeff)
      (rationalTwo childRightCoeff) = 0 := by
    rw [hchildRep, lowProduct_quarticProjection] at hchildQuartic
    exact hchildQuartic
  have htargetCubic := anfThreeProjection_eq_zero_of_mem_targetAmbient htarget
  have hlowCubic := anfThreeProjection_eq_zero_of_mem_targetAmbient
    (rationalLowSpace_le_targetAmbient hlow)
  have hchildCubic : anfThreeProjection child =
      anfThreeProjection (C.gate 3) := by
    have heq := congrArg anfThreeProjection htargetEq
    rw [map_add, map_add, hlowCubic, htargetCubic, zero_add] at heq
    exact ((add_eq_zero_iff_eq_neg.mp heq.symm).trans
      (by funext i j k; exact neg_eq_self_f2 _)).symm
  have htargetNonrational : ¬ IsRationalCoeff targetCoeff := by
    intro hrat
    rcases (IsRationalCoeff_iff targetCoeff).mp hrat with
      ⟨alpha, halpha⟩
    apply htargetNotLow
    rw [htargetRep, halpha]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left htargetAffine
    · apply Submodule.mem_sup_right
      exact (mem_rationalTargetSpace_iff _).mpr ⟨alpha, rfl⟩
  exact
    ⟨targetAffine, targetCoeff,
      child, low,
      childLeftConst, childRightConst, childLeftLinear, childRightLinear,
      childLeftCoeff, childRightCoeff,
      h.cubicSeedNormalForm, hlow, htargetAffine, hchildRep,
      htargetEq, htargetRep, hchildProbe, hchildCubic,
      h.seed_cubicProjection_ne_zero, htargetNonrational⟩

end
end N4
end UnrestrictedBooleanMul
end
