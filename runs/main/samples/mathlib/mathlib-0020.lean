public section

variable {α : Type*}

namespace Set

open scoped Function

section PairwiseDisjoint

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α] (a : α)

variable (α)

theorem pairwise_disjoint_Ioo_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ioo (n : α) (n + 1)) := by
  simpa only [zero_add] using pairwise_disjoint_Ioo_add_intCast (0 : α)

end OrderedRing
end PairwiseDisjoint
end Set
end
