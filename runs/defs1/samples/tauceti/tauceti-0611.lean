public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) {V : Type u} (G : SimpleGraph V) [Finite V]

variable [Field k]

/-- The vertex, outgoing-arrow and volume family in `Z e_i`. -/
noncomputable def zigzagProjectiveBasisFun (i : V) :
    ZigzagProjectiveBasisIndex G i → zigzagProjective k G i
  | .inl _ => zigzagProjectiveGenerator k G i
  | .inr (.inl d) =>
      ⟨zigzagMk k G (ofArrow (arrow G d.1.adj)),
        (mem_zigzagProjective_iff k G).2 (by
          simpa only [zigzagVertexIdempotent, d.2] using
            zigzagMk_ofArrow_mul_vertexIdempotent k G d.1)⟩
  | .inr (.inr _) =>
      ⟨zigzagVolume k G i,
        (mem_zigzagProjective_iff k G).2
          (zigzagVolume_mul_zigzagMk_vertexIdempotent k G i)⟩

end TauCeti
end
