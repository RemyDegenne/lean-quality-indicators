namespace OAI

section

section

open scoped symmDiff

namespace SimpleAmenable

open scoped commutatorElement

open scoped commutatorElement

section FiniteDirectRefinement

variable {G : Type*} [Group G]

theorem split_assignmentFactor {ι : Type*}
    (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    {C D : Subgroup G} (k : CommutingFactors C D) (hz : Subgroup.center G = ⊥)
    (S : Finset ι) {x : G} (hx : x ∈ assignmentFactor A S) :
    ∃ c ∈ assignmentFactor A S ⊓ C, ∃ d ∈ assignmentFactor A S ⊓ D, x = c*d := by
  refine ⟨k.projectLeft hz x, ⟨?_,k.projectLeft_mem hz x⟩,
    k.symm.projectLeft hz x, ⟨?_,k.symm.projectLeft_mem hz x⟩,k.projectLeft_split hz x⟩
  · exact projectLeft_mem_assignmentFactor A B h k hz S hx
  · exact projectLeft_mem_assignmentFactor A B h k.symm hz S hx

end FiniteDirectRefinement
end SimpleAmenable
end
end
end OAI
