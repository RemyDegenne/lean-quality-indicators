@[expose] public section

open Set Filter

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

variable (X)

export SeqCompactSpace (isSeqCompact_univ)

/-- A topological space is said to be a *sequential space* if any sequentially closed set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space. -/
class SequentialSpace : Prop where
  isClosed_of_seq : ∀ s : Set X, IsSeqClosed s → IsClosed s

end
