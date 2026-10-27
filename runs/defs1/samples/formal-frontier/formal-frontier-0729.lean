@[expose] public section

namespace Bundle.HermitianMetric

open ContinuousLinearEquiv (toEuclidean)

variable (𝕜 : Type*) [RCLike 𝕜]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A positive-definite continuous Hermitian form on a finite-dimensional normed space,
compatible with its existing topology. It is expressed as a metric on the trivial bundle over a
point, without changing the norm on the model space. -/
noncomputable def ofFiniteDimensional : HermitianMetric 𝕜 (Bundle.Trivial Unit F) where
  inner _ := (innerSL 𝕜).bilinearComp (toEuclidean 𝕜 F).toContinuousLinearMap
    (toEuclidean 𝕜 F).toContinuousLinearMap
  symm _ v w := inner_conj_symm (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F w)
  pos _ v hv := by
    change 0 < RCLike.re (Inner.inner 𝕜 (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F v))
    exact re_inner_self_pos.mpr (by
      simpa only [map_zero] using (toEuclidean 𝕜 F).injective.ne hv)
  continuousAt _ := by fun_prop
  isVonNBounded _ := by
    let c : InnerProductSpace.Core 𝕜 F :=
      { inner v w := Inner.inner 𝕜 (toEuclidean 𝕜 F v) (toEuclidean 𝕜 F w)
        conj_inner_symm v w := inner_conj_symm _ _
        re_inner_nonneg v := inner_self_nonneg
        add_left v w x := by simp only [map_add, inner_add_left]
        smul_left v w r := by simp only [map_smul, inner_smul_left]
        definite v hv := (toEuclidean 𝕜 F).injective (by
          simpa only [map_zero] using inner_self_eq_zero.mp hv) }
    exact c.isVonNBounded_unit_sublevel

end Bundle.HermitianMetric
end
