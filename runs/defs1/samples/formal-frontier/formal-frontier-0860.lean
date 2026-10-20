@[expose] public section

universe u v w

/-- A commutative ring is universally coherent (for target algebras in `Type v`) if every
finitely presented commutative algebra in that universe is a coherent ring.

The target-algebra universe is deliberately independent of the universe containing the base
ring. Use `IsUniversallyCoherent.{u, v} R` when that universe is not inferred from an algebra. -/
class IsUniversallyCoherent (R : Type u) [CommRing R] : Prop where
  isCoherentRing (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] : IsCoherentRing A

end
