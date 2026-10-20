@[expose] public noncomputable section

open MeasureTheory

open scoped MeasureTheory

open scoped Topology

namespace AleksandrovDifferentiability

theorem ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_directionalCluster
    {n : ℕ} (hfiniteStatement : ConvexFiniteUpperContactOpeningAEOnCubeStatement n)
    (hn : 1 ≤ n) {u : SourceCubeSpace n → ℝ}
    (hbounded : BoundedOn (sourceOpenCube n 3) u)
    (hconvex : ConvexOn ℝ (sourceOpenCube n 3) u)
    (hdom :
      ∀ (x : SourceCubeSpace n) (m : ℕ),
        x ∈ cubeGoodSet n u (m : ℝ) →
          ∀ᶠ y in 𝓝[sourceOpenCube n (3 / 2 : ℝ) \ {x}] x,
            ∀ p : SourceCubeSpace n, SubgradientOn (sourceOpenCube n 3) u y p →
              ∀ z : SourceCubeSpace n,
                ∃ q ∈
                  HasSubgradientLinearizationOnAt.GradientClusterSet
                    (sourceCubeDifferentiabilitySet n (3 / 2 : ℝ) u)
                    (frechetGradient u) y, inner ℝ p z ≤ inner ℝ q z) :
    ∀ᵐ x ∂(volume.restrict (sourceOpenCube n 1)),
      SecondOrderDifferentiableAt u x :=
  ae_restrict_sourceOpenCube_secondOrderDifferentiableAt_of_clusterDensity
    hfiniteStatement hn hbounded hconvex
    (fun x m hxgood =>
      HasSubgradientLinearizationOnAt.clusterDensity_of_eventually_directional_dominating_cluster
        (hdom x m hxgood))

end AleksandrovDifferentiability
end
