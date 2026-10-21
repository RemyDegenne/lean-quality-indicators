namespace OAI

section

namespace PlanarL1.Columns.Model.PairGeometry

open Parameters MeasureTheory VertexTests

attribute [local instance] Classical.propDecidable

variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}

variable [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}

variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)

variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)

variable (v : V → M.Point Set.univ A.root)

variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)

variable (q p : ℝ) (phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ)

lemma narrow_height (x : V) : (v x).height ∈ BandTrees.band narrow (narrowLower A v p x) := by
  have hh := Tiling.mem_band_index interpolationB.2.1 p (v x).height
  change p+(Tiling.index a₂ p (v x).height:ℝ)*a₂≤(v x).height ∧
    (v x).height≤p+(Tiling.index a₂ p (v x).height:ℝ)*a₂+a₂
  constructor <;> dsimp [Tiling.band] at hh <;> linarith [hh.1,hh.2]

end PlanarL1.Columns.Model.PairGeometry
end
end OAI
