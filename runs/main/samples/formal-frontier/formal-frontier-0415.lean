@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u v w

namespace Topology

namespace WithGenericPoint

variable {ι : Type v}

@[simp]
theorem generic_le (x : WithGenericPoint ι) : WithGenericPoint.generic ≤ x := Or.inl rfl

end WithGenericPoint
end Topology
end
