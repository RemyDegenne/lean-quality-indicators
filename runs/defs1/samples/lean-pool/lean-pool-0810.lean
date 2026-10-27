public section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators

open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

local instance : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩

noncomputable section

namespace CKN

/-- Multiply a smooth spatial test by the fixed scalar cutoff. -/
@[expose]
def weakContL3CutoffTest (χ : Vec3 → ℝ)
    (φ : weakContL3SmoothTest) : Vec3 → Vec3 :=
  fun x => χ x • weakContL3OfLp (φ.val x)

end CKN
end
end
