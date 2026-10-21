namespace OAI

noncomputable section

open Set MeasureTheory

open scoped ContDiff

namespace CubicFirstMoment

local instance complexLocalization_borel : MeasurableSpace CubicThetaTangent := borel CubicThetaTangent

local instance complexLocalization_borelSpace : BorelSpace CubicThetaTangent := ⟨rfl⟩

local instance complexLocalization_smoothGroup : AddCommGroup cubicThetaSmoothTests :=
  Module.addCommMonoidToAddCommGroup ℂ

variable {φ : ℂ × ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
  (hc : HasCompactSupport φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})

variable (e : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
  (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
  {S : Set CubicThetaPoint} (hS : IsCompact S) (hSe : S⊆e.source)
  (hsupp : tsupport φ⊆cubicThetaPointCoordinates '' S)

include e he hS hSe hsupp in
theorem cubicThetaComplexLocalInclusion_eq :
    (cubicThetaComplexLocalInclusion hφ hc hp : cubicThetaGlobalEnergySpace → LocalSobolev.TangentComplexL2)=
      cubicThetaGlobalLocalInclusion hφ hc hp := by
  apply cubicThetaGlobalEnergyTestLinear_dense.equalizer
    (cubicThetaComplexLocalInclusion hφ hc hp).continuous
    (cubicThetaGlobalLocalInclusion hφ hc hp).continuous
  funext F
  change cubicThetaComplexLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)=
    cubicThetaGlobalLocalInclusion hφ hc hp (cubicThetaGlobalEnergyTest F)
  rw [cubicThetaComplexLocalInclusion_test hφ hc hp e he hS hSe hsupp,
    cubicThetaGlobalLocalInclusion_test hφ hc hp e he hS hSe hsupp,cubicThetaLocalValue_apply]

end CubicFirstMoment
end
end OAI
