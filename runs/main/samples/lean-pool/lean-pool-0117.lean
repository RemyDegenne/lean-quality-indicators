public section

open MeasureTheory Filter

open scoped Interval ENNReal Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

local instance : MeasurableSpace RealVectorL2 := borel RealVectorL2

local instance : BorelSpace RealVectorL2 := ⟨rfl⟩

local instance : IsSeparable (volume : Measure L2Vec3) := by infer_instance

local instance : TopologicalSpace.SeparableSpace L2Vec3 := by infer_instance

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

local instance : SecondCountableTopology RealVectorL2 := by
  exact Lp.SecondCountableTopology

theorem mildShiftedStokesIntegral_continuous
    (F : ℝ → RealTensorL2) (hF : Continuous F) (C : ℝ)
    (hFC : ∀ t, ‖F t‖ ≤ C) (hC : 0 ≤ C) (T : ℝ) (hT : 0 ≤ T) :
    Continuous fun t => ∫ τ in (0 : ℝ)..T,
      mildShiftedStokesIntegrand F t τ := by
  rw [continuous_iff_continuousAt]
  intro t
  exact mildShiftedStokesIntegral_continuousAt F hF C hFC hC T hT

end CKN.Leray
end
end
