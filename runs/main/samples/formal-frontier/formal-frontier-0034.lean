@[expose] public section

universe u v

namespace Subcoalgebra

variable {K : Type u} {C : Type v}

variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

theorem comul_mem (D : Subcoalgebra K C) {x : C} (hx : x ∈ D) :
    Coalgebra.comul (R := K) x ∈
      LinearMap.range (TensorProduct.mapIncl D.toSubmodule D.toSubmodule) :=
  D.comul_mem' hx

end Subcoalgebra
end
