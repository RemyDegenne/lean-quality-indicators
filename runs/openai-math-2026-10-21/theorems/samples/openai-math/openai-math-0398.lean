namespace OAI

open Complex

open scoped ContDiff Matrix Matrix.Norms.Elementwise

open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder

open scoped ContDiff ComplexOrder

open scoped ContDiff ENNReal

open Set Filter Topology

open scoped ContDiff

open Set Filter Topology MeasureTheory

open scoped ContDiff ENNReal Pointwise

noncomputable section

open Set Filter Topology MeasureTheory

open scoped ContDiff ENNReal Pointwise

namespace PinchedHartogs.BaseConstruction

lemma adaptedHopf_integral {F : Sphere → ℂ} (hF : Continuous F) (p : Sphere) :
    (∫ ξ, F ξ ∂sigma) = ∫ t : unitInterval, ∫ z, F (adaptedHopf p t z) ∂torusMeasure := by
  rw [← sigma_integral_unitary (adaptedIsometry p).symm F]
  exact hopf_integral_complex (hF.comp (sphereAction _).continuous)

end PinchedHartogs.BaseConstruction
end
end OAI
