public section

set_option warningAsError true

open Filter Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}

@[simp]
theorem mem_cofiniteStage {s : Finset ι} {x : Πʳ i, [R i, A i]} :
    x ∈ cofiniteStage (R := R) (A := A) s ↔ ∀ i, i ∉ s → x i ∈ A i :=
  Iff.rfl

end RestrictedProduct
end
