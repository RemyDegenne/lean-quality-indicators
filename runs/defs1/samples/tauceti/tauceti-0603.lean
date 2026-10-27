public section

namespace TauCeti

/-- A **spherical parameter signature** is a sorted positive parameter triple whose first parameter
is `1`, or whose first two parameters are `2`, or which is one of the three polyhedral triples
`(2, 3, 3)`, `(2, 3, 4)` and `(2, 3, 5)`. These are exactly the presentation parameters of
positive orbifold Euler characteristic, by `TauCeti.isSphericalParameterSignature_iff`.

The first branch is a statement about presentation parameters, and the monodromy orders are only
required to divide the presentation parameters: among exact signatures it is therefore the
reduced form `(1, m, m)`, by
`TauCeti.PermutationTriple.geometryType_eq_spherical_iff_isSphericalSignature`.

The body is not exposed: the `Decidable` instance below is built from the characteristic formula,
and a signature is read through the same formula. -/
def IsSphericalParameterSignature (a b c : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧
    (a = 1 ∨ (a = 2 ∧ b = 2) ∨ (a, b, c) = (2, 3, 3) ∨ (a, b, c) = (2, 3, 4) ∨
      (a, b, c) = (2, 3, 5))

end TauCeti
end
