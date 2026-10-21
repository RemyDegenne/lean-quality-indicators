namespace OAI

noncomputable section

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

open scoped Classical

variable {A : Type*} {k : Kind}

namespace LocalRanks

@[ext] lemma ext_rank {d e : LocalRanks k} (h : d.rank=e.rank) : d=e := by
  cases d; cases e; cases h; rfl

end LocalRanks
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
end
end OAI
