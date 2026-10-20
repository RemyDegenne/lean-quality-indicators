public section

universe u v

namespace TauCeti

variable {K : Type u} [Field K]

namespace BrauerGroup

@[simp]
theorem mk_op (A : CSA.{u, u} K) : mk (CSA.op A) = (mk A)⁻¹ :=
  rfl

end BrauerGroup
end TauCeti
end
