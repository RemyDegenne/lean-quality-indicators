@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric

open scoped BigOperators ENNReal NNReal Topology

open CKN.Foundation.Parabolic

open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- The centred divergence-form source paired with `pressureUTensor u c`. -/
def pressureDivergenceCutoffSourceCentred
    (η : Vec3 → ℝ) (dη : Fin 3 → Vec3 → ℝ)
    (u : Vec3 → Vec3) (Du : Vec3 → Fin 3 → Vec3) (f : Vec3 → Vec3)
    (c : Vec3) : Vec3 → Vec3 :=
  fun x i => ∑ j, (η x * Du x i j * (u x j - c j) +
      dη j x * u x i * (u x j - c j)) - η x * f x i

end CKN.Core.Step4
end
end
