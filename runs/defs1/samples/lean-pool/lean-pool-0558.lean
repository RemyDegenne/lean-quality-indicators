@[expose] public section

noncomputable section PortComputability

namespace MarkovProcess

section MixedPastFutureCutCoordinates

open MeasureTheory ProbabilityTheory

open scoped ProbabilityTheory

namespace MixedPastFuture

section

/-- Sorted physical elapsed times of the strictly positive future. -/
def positiveFutureOrderedPhysicalTimes (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    FiniteOrderedTimes (positiveFutureFinset S I).card :=
  (Fin.castOrderIso (by
    rw [SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map])).toOrderEmbedding.trans
    (SubMarkovKernelSemigroup.finiteSetTimes
      (SubMarkovKernelSemigroup.denseTimePhysicalSet (positiveFutureFinset S I)))

end
end MixedPastFuture
end MixedPastFutureCutCoordinates
end MarkovProcess
end PortComputability
end
