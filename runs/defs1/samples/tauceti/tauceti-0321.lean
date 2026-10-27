public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N P : C}

/-- **The cup product on singular cohomology**,
`Hᵖ(X; R, M) × H^q(X; S, N) ⟶ Hⁿ(X; T, P)` for `p + q = n`: the cup product of cohomology classes
along the Alexander–Whitney diagonal `X.alexanderWhitneyDiagonal u` and the pairing
`μ : M ⊗ N ⟶ P`, `k`-bilinear and natural in `X` (`TopCat.singularCup_naturality`). -/
def singularCup (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCohomology R k M p →ₗ[k] X.singularCohomology S k N q →ₗ[k]
      X.singularCohomology T k P n :=
  TauCeti.ChainComplex.cup k (X.alexanderWhitneyDiagonal u) μ p q n h

end Cohomology
end TopCat
end
end
