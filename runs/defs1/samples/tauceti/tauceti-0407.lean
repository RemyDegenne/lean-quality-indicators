public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The Weierstrass curve `Y² + aXY + bY = X³ + bX²` in **Tate normal form**:
`a₁ = a`, `a₂ = a₃ = b` and `a₄ = a₆ = 0`. -/
def tateNormalForm (a b : R) : WeierstrassCurve R where
  a₁ := a
  a₂ := b
  a₃ := b
  a₄ := 0
  a₆ := 0

end WeierstrassCurve
end
