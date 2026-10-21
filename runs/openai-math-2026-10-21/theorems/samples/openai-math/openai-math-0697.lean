namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set

open scoped NNReal ENNReal

open Filter

open scoped Topology

open Matrix Real

open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal

open Matrix Real

open scoped BigOperators Matrix.Norms.Frobenius NNReal

open MeasureTheory ProbabilityTheory Real Set Filter

open MeasureTheory.Measure

open scoped ENNReal NNReal MeasureTheory Topology

open MeasureTheory

open MeasureTheory Set NormedSpace

open scoped Topology

open Matrix Real

open scoped BigOperators Matrix.Norms.Frobenius

namespace SKGap.ComplexMatrix

section

open MeasureTheory Set NormedSpace

open scoped Topology FourierTransform SchwartzMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  @SeminormedAddGroup.toContinuousENorm _ Matrix.frobeniusSeminormedAddCommGroup.toSeminormedAddGroup

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℂ))

lemma fourier_scalar_inverse (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (∫ t : ℝ, (𝓕 f) t * Complex.exp ((t : ℂ)*Complex.I*((2*Real.pi*x : ℝ) : ℂ))) = f x := by
  have hh := congrArg (fun g : 𝓢(ℝ,ℂ) => g x) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq'] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_eq_mul,Real.inner_apply]
  conv_lhs => rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

end
end SKGap.ComplexMatrix
end
end OAI
