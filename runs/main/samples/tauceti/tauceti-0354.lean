public section

namespace TauCeti

open scoped BigOperators

attribute [local instance] IsConj.setoid

variable {G : Type*} [Group G]

namespace ClassData

variable (d : ClassData G)

section Executable

variable [DecidableRel (IsConj : G → G → Prop)]

variable [Fintype G]

section Classes

theorem sum_card_classFinset : ∑ i, (d.classFinset i).card = Fintype.card G := by
  simp only [classFinset]
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise fun g _ => Finset.mem_univ (d.index g)).symm

end Classes
end Executable
end ClassData
end TauCeti
end
