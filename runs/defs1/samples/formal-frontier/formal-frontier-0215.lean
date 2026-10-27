public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

/-- The inclusion induced on invariant coefficients.
The application formula computes using the underlying equivariant inclusion. -/
@[expose]
def invariantsInclusion : A.ρ.invariants →L[k] B.ρ.invariants :=
  S.i.hom.mapInvariants

end TopologicallySplitShortExact
end ContinuousCohomology
end
