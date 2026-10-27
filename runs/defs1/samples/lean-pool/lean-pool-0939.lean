@[expose] public section

namespace Erdos132ThreeChain

open Finset

/-- Adjacency in the diameter graph: distinct points at squared distance exactly `D`. -/
def DiameterAdj (D : ℝ) (p q : Point) : Prop := p ≠ q ∧ sqDist p q = D

end Erdos132ThreeChain
end
