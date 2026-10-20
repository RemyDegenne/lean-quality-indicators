public section

open scoped DirectSum

namespace TauCeti

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- Project a grid chain onto one homogeneous piece. -/
noncomputable def bigradedChainProjection (R : Type*) [Semiring R] (g : ℤ × ℤ) :
    GridChain R n →ₗ[R] G.BigradedChainPiece R g :=
  (DirectSum.component R (ℤ × ℤ) (G.BigradedChainPiece R) g).comp
    (G.bigradedChainEquiv R).toLinearMap

end OddComponentGridDiagram
end TauCeti
end
