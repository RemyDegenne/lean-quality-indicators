namespace OAI

noncomputable section

open scoped Topology

open Filter

open Filter MeasureTheory

open UniformSpace

open scoped ContDiff

open MeasureTheory

open MeasureTheory Set

open MeasureTheory Set Filter

open scoped Topology Interval

open Set Filter

open UniformSpace Set

open UniformSpace Filter

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressCutoff_difference (hc : A.toVertexAlgebra.C2Cofinite) (n m : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖(U.stressCutoff hc n hf-U.stressCutoff hc m hf)*U.inverseSobolev 2‖ ≤
      ((1+(n:ℝ))⁻¹+(1+(m:ℝ))⁻¹)*((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re)) := by
  have he : (U.stressCutoff hc n hf-U.stressCutoff hc m hf)*U.inverseSobolev 2 =
      (U.stressCutoff hc n hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2)-
      (U.stressCutoff hc m hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2) := by noncomm_ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add (U.stressCutoff_error hc n hf)
    (U.stressCutoff_error hc m hf)).trans_eq (by ring))

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
end
end OAI
