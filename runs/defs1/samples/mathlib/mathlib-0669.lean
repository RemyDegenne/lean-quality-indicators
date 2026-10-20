public section

open ContinuousMap

variable {X Y R E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Module R E]

namespace AbstractMeasure

section ContinuousSMul

variable [ContinuousSMul R E]

section Map

/-- Measures can be pushed forward (`R`-linearly) along continuous maps. -/
def map (f : C(X, Y)) : AbstractMeasure X R E →ₗ[R] AbstractMeasure Y R E where
  toFun μ := μ ∘L f.compCLM R R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Map
end ContinuousSMul
end AbstractMeasure
end
