@[expose] public section

variable {ι : Sort*} {F α β : Type*}

open Finset OrderDual

section SemilatticeSup

variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

@[to_dual (attr := simp)]
lemma supClosure_univ : supClosure (Set.univ : Set α) = Set.univ := by simp

end SemilatticeSup
end
