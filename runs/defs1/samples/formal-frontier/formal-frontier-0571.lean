public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

/-- Replace the chosen underlying section without changing the exact
coefficient sequence. -/
def withSection (s : C →L[k] B) (hs : ∀ c, S.p (s c) = c) :
    TopologicallySplitShortExact A B C :=
  { S with section_ := s, p_section := hs }

end TopologicallySplitShortExact
end ContinuousCohomology
end
