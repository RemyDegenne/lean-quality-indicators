@[expose] public section

namespace TMB

universe u v

open Multiset Finset

/-- The six ordered placements that can have general transmission on a
rigid wedge of two genus-one factors. -/
def WedgeKGeneralPlacement
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ) : Prop :=
  (∃ a : G.V, u = Sum.inl x ∧ v = Sum.inl a ∧ a ≠ x ∧
    Fintype.card G.V = 2 ∧ k = 2) ∨
  (∃ a : G.V, u = Sum.inl a ∧ v = Sum.inl x ∧ a ≠ x ∧
    Fintype.card G.V = 2 ∧ k = 2) ∨
  (∃ p : H.V, u = wedgeRightVertex G H x y y ∧
    v = wedgeRightVertex G H x y p ∧ p ≠ y ∧
    Fintype.card H.V = 2 ∧ k = 2) ∨
  (∃ p : H.V, u = wedgeRightVertex G H x y p ∧
    v = wedgeRightVertex G H x y y ∧ p ≠ y ∧
    Fintype.card H.V = 2 ∧ k = 2) ∨
  (∃ a : G.V, ∃ p : H.V, u = Sum.inl a ∧
    v = wedgeRightVertex G H x y p ∧ a ≠ x ∧ p ≠ y ∧
    ∃ r : ℕ, IsTorsionOrder (mark G a x) r ∧
      IsTorsionOrder (mark H y p) r ∧ k = r) ∨
  (∃ a : G.V, ∃ p : H.V, u = wedgeRightVertex G H x y p ∧
    v = Sum.inl a ∧ a ≠ x ∧ p ≠ y ∧
    ∃ r : ℕ, IsTorsionOrder (mark G a x) r ∧
      IsTorsionOrder (mark H y p) r ∧ k = r)

end TMB
end
