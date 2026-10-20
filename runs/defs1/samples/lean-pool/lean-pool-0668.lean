@[expose] public section

open MeasureTheory

open ProbabilityTheory

open scoped ENNReal

namespace ChannelCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace Kernel

/-- Pairwise-distinct rows of a kernel. This is weaker than injective prior pushforward. -/
def RowSeparating (k : Kernel α β) : Prop :=
  ∀ ⦃a a' : α⦄, a ≠ a' → k a ≠ k a'

end Kernel
end ChannelCapacity
end
