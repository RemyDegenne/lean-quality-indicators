@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

/-- A local certificate on one rectangle of second-child radii. -/
structure GramCertificate where
  /-- Lower bound for the second red radius. -/
  pLower : ℚ
  /-- Upper bound for the second red radius. -/
  pUpper : ℚ
  /-- Lower bound for the second blue radius. -/
  wLower : ℚ
  /-- Upper bound for the second blue radius. -/
  wUpper : ℚ
  /-- Tangent parameter for `e - p₁ - w₁`. -/
  alpha₀ : ℚ
  /-- Tangent parameter for `e - p₂ - w₂`. -/
  alpha₁ : ℚ
  /-- Tangent parameter for `e - p₁`. -/
  alpha₂ : ℚ
  /-- Tangent parameter for `e - w₁`. -/
  alpha₃ : ℚ
  /-- Tangent parameter for `e - p₁ - w₂`. -/
  alpha₄ : ℚ
  /-- Tangent parameter for `e - w₁ - p₂`. -/
  alpha₅ : ℚ
  /-- Multiplier for the red separation constraint. -/
  etaP : ℚ
  /-- Multiplier for the blue separation constraint. -/
  etaW : ℚ
  /-- The rank-three rational Gram factor. -/
  factor : Fin 3 → Fin 5 → ℚ

end LeanPool.Besicovitch
end
end
