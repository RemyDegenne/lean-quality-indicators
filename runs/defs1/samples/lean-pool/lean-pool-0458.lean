@[expose] public section

noncomputable section PortComputability

namespace MarkovProcess

section MixedPastFutureCoordinates

open MeasureTheory

section

namespace MixedPastFuture

/-- The finite set of absolute dense times observed by a mixed past/future coordinate set. -/
def absoluteFinset (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Finset DenseTime :=
  pastFinset S I ∪ DenseTime.addFinset S (futureFinset S I)

end MixedPastFuture
end
end MixedPastFutureCoordinates
end MarkovProcess
end PortComputability
end
