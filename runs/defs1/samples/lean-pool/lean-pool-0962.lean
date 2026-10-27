@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

open Filter

open scoped Topology

namespace MovingSofa

/-- The cap is a Hausdorff limit of polygonal maxima on increasingly fine dyadic meshes. -/
def IsBalancedMaximumCap {ω : ℝ} (K : CapSpace ω) : Prop :=
  ∃ (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i), StrictMono n ∧
    (∀ i, ∃ k : ℕ, n i = 2 ^ k) ∧
    ∃ P : ∀ i, PolygonCapSpace (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)),
      (∀ i, IsMaximumPolygonCap _ (P i)) ∧
      Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point) (K.val : Set Point))
        atTop (𝓝 0)

end MovingSofa
end
end
end
end
end
end
end
end
