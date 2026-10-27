@[expose] public section

namespace KaltonPeck.Support

noncomputable
section

namespace Coordinates

/-- The fixed project-normalized canonical real Kalton--Peck carrier.
Blueprint label: `thm:kp-canonical-banach`; audit ID `INF-KP-CANONICAL-MODEL`. -/
def CanonicalRealKaltonPeck : Type := by
  exact {p : (ℕ → ℝ) × (ℕ → ℝ) // IsAdmissiblePair p}

end Coordinates
end
end KaltonPeck.Support
end
