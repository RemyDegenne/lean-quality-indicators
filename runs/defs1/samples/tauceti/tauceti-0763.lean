public section

namespace TauCeti.FiniteQuadraticModule

variable (k : ℕ)

/-- The group `(ℤ/2^k)²` with quadratic form `q(x) = x₁x₂ / 2^k` and pairing
`b(x, y) = (x₁y₂ + y₁x₂) / 2^k`. For `k ≥ 1` this is **Nikulin's dyadic generator**
`u^{(2)}(2^k)`, the discriminant form of the `2`-adic lattice with Gram matrix
`2^k·!![0,1;1,0]`, the hyperbolic plane scaled by `2^k`. -/
@[expose] noncomputable def dyadicU : FiniteQuadraticModule :=
  ofQuadraticMap <| (ZMod.toRatAddCircle (2 ^ k)).toIntLinearMap.compQuadraticMap
    (QuadraticMap.linMulLin
      (AddMonoidHom.fst (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap
      (AddMonoidHom.snd (ZMod (2 ^ k)) (ZMod (2 ^ k))).toIntLinearMap)

end TauCeti.FiniteQuadraticModule
end
