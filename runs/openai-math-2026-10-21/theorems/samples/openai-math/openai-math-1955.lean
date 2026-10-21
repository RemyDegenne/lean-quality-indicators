namespace OAI

noncomputable section

namespace YauCounterexamples

section

open Set Filter Function

open scoped Topology ContDiff Manifold SchwartzMap

open Set Filter Manifold Bundle MeasureTheory NNReal

open scoped Topology ContDiff ENNReal

open Set Filter Topology NNReal

open Set Filter Module

open scoped Topology

open Set Filter Manifold Bundle MeasureTheory

open scoped Topology ContDiff ENNReal

open Set Filter

open scoped Topology ContDiff

open Set Filter Function

open scoped Topology ContDiff Manifold

open Set Filter Function

open scoped Topology ContDiff Manifold Matrix

open Set Filter Function

open scoped Topology ContDiff Manifold Matrix

open Set Filter Function

open scoped Topology ContDiff Manifold Matrix

open Set Filter

open scoped Topology

open Set Filter Function MeasureTheory FourierTransform TemperedDistribution

open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction

open Set Filter Function

open scoped Topology ContDiff Manifold

open Set Filter Manifold Bundle Matrix

open scoped Topology ContDiff

open Set Filter Function Manifold

open scoped Topology ContDiff InnerProductSpace

variable {d : ℕ}

local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma round_metricCoefficients_at (g : SmoothMetric (Euclidean d) (Sphere d)) (p : Sphere d)
    (hg : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) p),
      g.inner p v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) p w)) :
    metricCoefficients g p 0 = Matrix.gram ℝ (Module.finBasis ℝ (Euclidean d)) := by
  have hp : (chartAt (Euclidean d) p).symm 0 = p := by
    simpa only [sphere_chart_center] using (chartAt (Euclidean d) p).left_inv (mem_chart_source _ p)
  have hg' : ∀ (v w : TangentSpace 𝓘(ℝ,Euclidean d) ((chartAt (Euclidean d) p).symm 0)),
      g.inner ((chartAt (Euclidean d) p).symm 0) v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) ((chartAt (Euclidean d) p).symm 0) w) := by
    change (fun q : Sphere d => ∀ v w : TangentSpace 𝓘(ℝ,Euclidean d) q,
      g.inner q v w = (inner ℝ : Euclidean (d+1) → Euclidean (d+1) → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q v)
        (mfderiv 𝓘(ℝ,Euclidean d) 𝓘(ℝ,Euclidean (d+1)) (fun q : Sphere d => (q : Euclidean (d+1))) q w))
      ((chartAt (Euclidean d) p).symm 0)
    rw [hp]
    exact hg
  let : ContinuousSMul ℝ (Euclidean d) := IsBoundedSMul.continuousSMul
  let : ContinuousSMul ℝ (Euclidean (d+1)) := IsBoundedSMul.continuousSMul
  have hround : fderiv ℝ (roundChart (p : Euclidean (d+1)) (sphereFrame p)) 0 =
      (sphereFrame p).toContinuousLinearMap :=
    (roundChart_first (p : Euclidean (d+1)) (sphereFrame p)).fderiv
  ext i j
  rw [metricCoefficients,hg']
  rw [coordinateVector,coordinateVector,sphere_coordinate_embedding p 0,
    sphere_coordinate_embedding p 0,hround]
  exact (sphereFrame p).inner_map_map _ _

end
end YauCounterexamples
end
end OAI
