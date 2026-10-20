@[expose] public section

open CategoryTheory AlgebraicTopology Limits Metric

open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

namespace SphereOddDegree

variable (n : ℕ)

/-- **The Mayer–Vietoris recursive step.** For `n ≥ 1`,
`Hₙ₊₁(Sⁿ⁺¹; ℤ) ≅ Hₙ(Sⁿ; ℤ)`. -/
def sphereTopHomologyStepMV (hn : 1 ≤ n) :
    sphereTopHomologyℤ (n + 1) ≅ sphereTopHomologyℤ n :=
  sphereModelHomologyIso (n + 1) (n + 1)
    ≪≫ mvHomologyIsoSucc ℤ (upperOpens n) (lowerOpens n) (upperOpens_sup_lowerOpens n) n
        (isZero_subChainComplex_homology_of_contractible _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractible _ _ (n + 1) (by omega))
        (isZero_subChainComplex_homology_of_contractible _ _ n hn)
        (isZero_subChainComplex_homology_of_contractible _ _ n hn)
    ≪≫ bandHomologyIso n

end SphereOddDegree
end
end
