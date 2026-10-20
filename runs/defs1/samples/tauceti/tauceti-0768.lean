public section

open CategoryTheory ContRepresentation

namespace TauCeti.ContCohomology

open TopRep _root_.ContinuousCohomology

open TauCeti.ContinuousCohomology (coeffMap coeffMap_def)

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ)

/-- The continuous cohomology of the underlying additive representation of `X` is the continuous
cohomology of `X`, as an additive equivalence between the carriers. -/
noncomputable def restrictScalarsIntEquiv :
    continuousCohomology n (restrictScalarsInt.obj X) ≃+ continuousCohomology n X :=
  (restrictScalarsIntIso X n).toContinuousLinearEquiv.toAddEquiv

end TauCeti.ContCohomology
end
