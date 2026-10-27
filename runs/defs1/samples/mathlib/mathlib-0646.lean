@[expose] public section

noncomputable section

open scoped Topology ContDiff

open Set ChartedSpace

section DerivativesDefinitions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M']

open scoped Manifold

variable (I I') in
/-- `MDifferentiableOn I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `DifferentiableOn` to manifolds. -/
def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x

end DerivativesDefinitions
end
end
