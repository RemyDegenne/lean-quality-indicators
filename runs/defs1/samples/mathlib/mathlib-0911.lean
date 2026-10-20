@[expose] public section

noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C]

attribute [instance 100] HasKernels.has_limit HasCokernels.has_colimit

section HasCokernels

variable [HasCokernels C]

set_option backward.defeqAttrib.useBackward true in
/-- The cokernel projection is natural. -/
@[simps] def coker.π : Arrow.rightFunc ⟶ coker (C := C) where app f := cokernel.π _

end HasCokernels
end CategoryTheory.Limits
end
end
