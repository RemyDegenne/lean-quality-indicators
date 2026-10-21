namespace OAI

noncomputable section

open scoped Topology

open Filter

namespace TotientAsymptotic

theorem extracted_structure_exception_small :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      preimageExceptionCount x (extractedStructureCondition x P) ≤
        ε*tupleNormalization x := by
  obtain ⟨C,_hC,hcount⟩ := ford_structure_exception_count
  intro ε hε
  have hlim : Tendsto (fun P : ℕ => C*Real.exp (-(P:ℝ)^2/4)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ppt_natural_gaussian_tendsto.const_mul C
  filter_upwards [fixed_model_band_exception_small (ε/2) (half_pos hε),
    hlim.eventually (eventually_lt_nhds (half_pos hε))] with P hband hsmall
  filter_upwards [hband,hcount,scale_eventually_pos,
    m_tendsto.eventually (eventually_gt_atTop P)] with x hb hx hn hm
  have hs : preimageExceptionCount x (extractedSimplexCondition x P) ≤
      (ε/2)*tupleNormalization x := by
    calc
      _ ≤ preimageExceptionCount x (fordSimplexCondition x P) :=
        preimageExceptionCount_mono (fun _ hh => fordSimplexCondition_implies_extracted hm hh)
      _ ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(P:ℝ)^2/4) := hx P hm
      _ = (C*Real.exp (-(P:ℝ)^2/4))*tupleNormalization x := by
        unfold tupleNormalization
        ring
      _ ≤ (ε/2)*tupleNormalization x := mul_le_mul_of_nonneg_right hsmall.le hn.le
  calc
    _ ≤ preimageExceptionCount x (modelBandsCondition x P)+
        preimageExceptionCount x (extractedSimplexCondition x P) :=
      preimageExceptionCount_and_le x _ _
    _ ≤ (ε/2)*tupleNormalization x+(ε/2)*tupleNormalization x := add_le_add hb hs
    _ = ε*tupleNormalization x := by ring

end TotientAsymptotic
end
end OAI
