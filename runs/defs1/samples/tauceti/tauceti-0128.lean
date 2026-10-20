public section

noncomputable section

open CategoryTheory Limits Module

universe w

namespace TauCeti

variable {k : Type w} [CommRing k] (R N : ModuleCat.{w} k) [Module.Projective k R]
  {M : Type w} [TopologicalSpace M] [T1Space M] {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : OpenPartialHomeomorph M E) {x : M}
  (hx : x ∈ φ.source)

/-- **Local cohomology is the dual of local homology**: at a point with a chart to a
finite-dimensional real normed space, the relative Kronecker map is a `k`-linear equivalence
`Hⁿ(M, M ∖ {x}; R, N) ≃ₗ[k] (Hₙ(M, M ∖ {x}; R) ⟶ N)`, for projective coefficients `R`. -/
def singularCohomologyComplSingletonKroneckerEquiv (n : ℕ) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularCohomology R k N n ≃ₗ[k]
      ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R n ⟶ N) :=
  haveI := projective_singularHomology_complSingleton R φ hx
  TopPair.singularKroneckerEquivOfProjectiveHomology _ R N n

end TauCeti
end
end
