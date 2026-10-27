public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

/-- Replace the chosen underlying retraction without changing the exact
coefficient sequence. -/
def withRetract (r : B →L[k] A) (hr : ∀ a, r (S.i a) = a) :
    TopologicallySplitShortExact A B C :=
  { S with retract := r, retract_i := hr }

end TopologicallySplitShortExact
end ContinuousCohomology
end
