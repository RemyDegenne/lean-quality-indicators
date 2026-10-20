public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

@[simp]
lemma invariantsProjection_apply (b : B.ρ.invariants) :
    S.invariantsProjection b = S.p b := rfl

end TopologicallySplitShortExact
end ContinuousCohomology
end
