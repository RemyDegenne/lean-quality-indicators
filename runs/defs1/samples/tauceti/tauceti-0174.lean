public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]

/-- **Invariant dimension after tensoring with `A`.** This additive homomorphism sends a class
`[M]` to `dimₖ (M ⊗ A)ᴳ`. -/
noncomputable def finrankTensorInvariantsK0 (A : FDRep k G) :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  (finrankInvariantsK0 (k := k) (G := G)).comp
    (AddMonoidHom.mulRight (fdRepK0RingEquiv k G (ExactK0.of A)))

end TauCeti
end
