@[expose] public section

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

namespace LinearEquiv

open LinearMap LinearMap.transvection Module Submodule

section dilatransvections

theorem transvection_mem_dilatransvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv ∈ dilatransvections R V :=
  transvections_subset_dilatransvections transvection_mem_transvections

end dilatransvections
end LinearEquiv
end
