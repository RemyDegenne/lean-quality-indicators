public section

set_option warningAsError true

open Filter Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} {A : (i : ι) → Set (R i)}

/-- A canonical finite exceptional set for an element of a cofinite restricted product. -/
noncomputable def exceptionalFinset (x : Πʳ i, [R i, A i]) : Finset ι :=
  (Filter.eventually_cofinite.mp x.2).toFinset

end RestrictedProduct
end
