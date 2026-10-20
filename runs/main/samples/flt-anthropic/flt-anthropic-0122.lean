namespace P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_E6v20self

p2m_open

p2m_open

open scoped NNReal ENNReal Pointwise

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace M4aD2Skeleton

open M4aD2Glue M4aD2GlueC

theorem zetaIntegral_eq_setIntegral_theta' (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous ⇑χ)
    (hχu : IsUnitaryChar (𝓞 F) F χ) (hχF : IsIdeleClassChar (𝓞 F) F χ)
    {D' : Set (AdeleRing (𝓞 F) F)ˣ} (hD'm : MeasurableSet D')
    (hD' : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' ν)
    (s : ℂ) (hs : 1 < s.re) :
    TateGlobal.zetaIntegral ν f χ s
      = ∫ x in D', M4aD2GlueC.ThetaSum F f x
          * (((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ∂ν := by
  have hFsInt : Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ =>
      f ↑x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν :=
    NumberField.TateGlobal.integrable_zetaIntegrand F ν hf hχc hχu hs
  have h0 : TateGlobal.zetaIntegral ν f χ s
      = ∫ x, (f ↑x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ∂ν := by
    rfl
  rw [h0, M4aD2Glue.integral_eq_setIntegral_tsum_smul hD' hFsInt]
  refine MeasureTheory.setIntegral_congr_fun hD'm fun x _ => ?_
  have hterm : ∀ a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
      f ↑(a • x) * ((χ (a • x) : ℂˣ) : ℂ) * ((ideleNorm F (a • x) : ℝ) : ℂ) ^ s
        = f ↑(x * ↑a) * (((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) := by
    intro a
    rw [show a • x = ↑a * x from rfl, chi_mul_principal F hχF a x,
      ideleNorm_mul_principal F a x,
      show (↑a : (AdeleRing (𝓞 F) F)ˣ) * x = x * ↑a from mul_comm _ _, mul_assoc]
  rw [tsum_congr hterm, tsum_mul_right]
  rfl

end M4aD2Skeleton
end Fold_E6v20self
end P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe
