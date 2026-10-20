public section

namespace TauCeti

open Set

open scoped ENNReal

section IsCurveJoining

variable {X : Type*} [TopologicalSpace X] {γ : ℝ → X} {x y : X}

theorem isCurveJoining_extend (γ : Path x y) : IsCurveJoining γ.extend x y where
  continuousOn := γ.continuous_extend.continuousOn
  source := γ.extend_zero
  target := γ.extend_one

end IsCurveJoining
end TauCeti
end
