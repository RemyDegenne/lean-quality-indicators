public section

namespace TauCeti

universe u v w

open SimpleGraph

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

/-- The component algebra of a nontrivial component, as an algebra equivalence rather than an
equality of bundled objects. -/
noncomputable def zigzagComponentAlgebraEquivNonisolated (C : G.ConnectedComponent)
    [Nontrivial C] :
    zigzagComponentAlgebra k G C ≃ₐ[k] nonisolatedZigzagQuotient k C.toSimpleGraph :=
  CategoryTheory.Iso.toAlgEquiv <|
    CategoryTheory.eqToIso (zigzagComponentAlgebra_eq_nonisolated k G C)

end TauCeti
end
