public section

namespace TauCeti

open Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

namespace GlTraceTwist

section Carrier

variable {R : Type u} {ι : Type*} {c : R} {M : Type v}

variable (ι c M) in
/-- The additive groups of a module and of its trace twist agree. -/
protected def addEquiv [AddCommGroup M] : GlTraceTwist ι c M ≃+ M where
  __ := GlTraceTwist.equiv ι c M
  map_add' _ _ := rfl

end Carrier
end GlTraceTwist
end TauCeti
end
