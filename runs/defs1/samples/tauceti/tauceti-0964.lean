public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] (S : ShortComplex (TopModuleCat R))

section descHomology

variable {W : Type*} [AddCommGroup W] [Module R W]

/-- **Descent of a linear map to homology.** A linear map out of the cycles of a short complex of
topological modules that vanishes on the kernel of the class map `S.homologyπ` descends to a linear
map out of the homology, with `descHomologyₗ_π` as its defining equation. Unlike Mathlib's
`CategoryTheory.ShortComplex.descHomology`, the target is an arbitrary module rather than an object
of `TopModuleCat R`, so that maps into spaces of linear maps can be descended. -/
noncomputable def descHomologyₗ (k : S.cycles →ₗ[R] W) (hk : ∀ z, S.homologyπ z = 0 → k z = 0) :
    S.homology →ₗ[R] W :=
  (S.toCycles.hom.range.liftQ k
    (show S.toCycles.hom.range ≤ LinearMap.ker k from fun z hz ↦
      LinearMap.mem_ker.2 (hk z (S.homologyπ_eq_zero_iff.2 (LinearMap.mem_range.1 hz))))).comp
    (homologyIsoCoker S).toContinuousLinearEquiv.toLinearEquiv.toLinearMap

end descHomology
end CategoryTheory.ShortComplex
end
