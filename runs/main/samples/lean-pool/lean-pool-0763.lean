@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology

open scoped ENNReal NNReal ZeroAtInfty

section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

section Embedding

variable {X₀ X₁ : Type*}

theorem injective_compactifiedEmbedding {iota : X₀ → X₁} (hiota : Function.Injective iota) :
    Function.Injective (compactifiedEmbedding iota) :=
  OnePoint.coe_injective.comp hiota

end Embedding
end MarkovProcess.PositiveC0ContractiveResolvent
end
end PortComputability
end
