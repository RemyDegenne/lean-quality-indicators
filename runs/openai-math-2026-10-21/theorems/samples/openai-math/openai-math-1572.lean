namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

open scoped BigOperators TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile

variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

theorem recursiveParameter_le_next_degree_seed (Cprimitive exponent innerDepth j : ℕ)
    {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hprimitive : source.Cprimitive = Cprimitive)
    (hschedule : source.scheduleExponent = exponent)
    (hseed : source.x = candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * j + 1) x) :
    source.recursiveParameter ≤ candidateNestedForwardSeed exponent
      degreeSourceCountConstants innerDepth (2 * (j + 1)) x := by
  simpa only [show 2 * j + 1 + 1 = 2 * (j + 1) by omega] using
    source.recursiveParameter_le_next_seed Cprimitive exponent innerDepth (2 * j + 1)
      hExponent hdepth hx hprimitive hschedule hseed

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial
end
end OAI
