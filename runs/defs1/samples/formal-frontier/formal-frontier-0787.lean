@[expose] public section

universe u v

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The comultiplication restricted to the tensor square of a subcoalgebra. -/
noncomputable def comul (D : Subcoalgebra K C) :
    D.toSubmodule →ₗ[K] D.toSubmodule ⊗[K] D.toSubmodule :=
  ((Coalgebra.comul (R := K) (A := C)).domRestrict D.toSubmodule).codLift
    (TensorProduct.mapIncl D.toSubmodule D.toSubmodule)
    (Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule)
    (fun x => D.comul_mem' x.property)

end Subcoalgebra
end
