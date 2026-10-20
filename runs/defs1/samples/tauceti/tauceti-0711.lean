public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => nonisolatedZigzagQuotient k G

/-- Right multiplication by the volume class `x_i`, as an endomorphism of the vertex projective
`P_i = Z e_i`. -/
noncomputable def zigzagProjectiveVolumeMul (i : V) :
    zigzagProjective k G i →ₗ[Z] zigzagProjective k G i :=
  (zigzagProjectiveHomEquivCorner k G i i).symm
    ⟨zigzagVolume k G i, zigzagVolume_mem_zigzagCorner k G i⟩

end TauCeti
end
