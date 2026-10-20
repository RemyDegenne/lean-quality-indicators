@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComoduleHom

section FieldCarrier

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]

variable {X : RightComodule K C M} {Y : RightComodule K C N}

theorem coefficientSubcoalgebra_toSubmodule_le_of_surjective
    (f : RightComoduleHom X Y) (hf : Function.Surjective f) :
    Y.coefficientSubcoalgebra.toSubmodule ≤ X.coefficientSubcoalgebra.toSubmodule := by
  simpa only [RightComodule.coefficientSubcoalgebra_toSubmodule] using
    f.coefficientSpan_le_of_surjective hf

end FieldCarrier
end Coalgebra.RightComoduleHom
end
