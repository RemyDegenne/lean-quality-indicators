set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous cohomology after canonical common-universe normalization. -/
noncomputable abbrev normalizedContinuousCohomology
    (X : TopRep.{w} k G) (n : ℕ) : TopModuleCat.{max v w} k :=
  continuousCohomology n (normalized X)

end TopRep
end
