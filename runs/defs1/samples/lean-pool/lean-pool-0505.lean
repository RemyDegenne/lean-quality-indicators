@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory.Kernel ProbabilityTheory

open Finset NNReal ENNReal Preorder Function StochasticMatrix Filter

namespace ProbabilityTheory

namespace MarkovChain

namespace Finite

universe u

variable {S : Type u}

variable [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Vector representation of the initial distribution of a finite Markov chain. -/
def initVec (M : HomMarkovChainSpec S)
  : S → ℝ :=
  fun s => (M.init {s}).toReal

end Finite
end MarkovChain
end ProbabilityTheory
end
