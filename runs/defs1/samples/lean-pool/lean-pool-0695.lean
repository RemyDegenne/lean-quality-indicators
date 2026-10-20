@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Multiply one signed measure by each of two scalar densities. -/
def pairFunctionMeasureMul {X : Type*} [MeasurableSpace X]
    (f : (X → ℝ) × (X → ℝ)) (μ : SignedMeasure X) :
    SignedMeasure X × SignedMeasure X :=
  (functionMeasureMul f.1 μ, functionMeasureMul f.2 μ)

end MovingSofa
end
end
end
end
end
end
end
end
end
end
end
