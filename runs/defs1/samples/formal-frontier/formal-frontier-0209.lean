public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

section Connecting

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Cohomology

variable [LocallyCompactSpace G]

/-- The connecting map from invariant quotient coefficients to mathlib's
first continuous cohomology object. Its application factors through
the crossed-homomorphism quotient. -/
@[expose]
noncomputable def connectingMap [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    TopModuleCat.of k C.ρ.invariants ⟶ continuousCohomology 1 A :=
  TopModuleCat.ofHom S.connectingQuotient ≫ (degreeOneIso A).hom

end Cohomology
end Connecting
end TopologicallySplitShortExact
end ContinuousCohomology
end
