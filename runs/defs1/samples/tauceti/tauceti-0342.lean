public section

namespace TauCeti

open PathAlgebra DoubledQuiver Polynomial

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **The homomorphisms `Z e_i → Z e_j` are the corner `e_i Z e_j`**, by evaluation at the
generator `e_i`.  This is the dictionary through which the corners computed by
`TauCeti.RepresentationTheory.Quiver.Zigzag.CartanMatrix` are homomorphism spaces of the vertex
projectives. -/
noncomputable def zigzagProjectiveHomEquivCorner (i j : V) :
    (zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G] zigzagProjective k G j) ≃ₗ[k]
      zigzagCorner k G i j :=
  (zigzagProjectiveHomEquivSpanSingletonHom k G i j).trans
    ((spanSingletonHomEquivCorner (zigzagMk_vertexIdempotent_mul_self k G i)
        (zigzagMk_vertexIdempotent_mul_self k G j)).trans
      (zigzagCornerEquivCornerSubmodule k G i j).symm)

end TauCeti
end
