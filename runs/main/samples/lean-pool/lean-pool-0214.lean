section

@[expose] public section

noncomputable section

namespace EulerSobolevWordConstraints

open EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerDivergenceFreeHeat

variable (period : ℝ) [Fact (0 < period)]

theorem sobolevGradientProjection_value {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    value period (sobolevGradientProjection period q κ m u) = gradientProjection period κ m (value
        period u) := rfl

end EulerSobolevWordConstraints
end
end
end
