@[expose] public section

universe u v

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The coalgebra on the underlying submodule subtype of a subcoalgebra, with the restricted
comultiplication and counit. -/
@[instance_reducible]
noncomputable def coalgebra (D : Subcoalgebra K C) : Coalgebra K D.toSubmodule where
  comul := D.comul
  counit := D.counit
  coassoc := D.coassoc
  rTensor_counit_comp_comul := D.rTensor_counit_comp_comul
  lTensor_counit_comp_comul := D.lTensor_counit_comp_comul

end Subcoalgebra
end
