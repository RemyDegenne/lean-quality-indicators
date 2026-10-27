@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The inclusion of a subcoalgebra into its ambient coalgebra. -/
noncomputable def subtype (D : Subcoalgebra K C) : D →ₗc[K] C where
  toLinearMap := D.toSubmodule.subtype
  counit_comp := D.coalgebra_counit_comp_subtype
  map_comp_comul := D.mapIncl_comp_coalgebra_comul

end Subcoalgebra
end
