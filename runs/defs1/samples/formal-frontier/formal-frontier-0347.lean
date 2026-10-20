public section

set_option warningAsError true

open Filter Function Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}

variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]

variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))

variable (e : ∀ i, X i →* Y i →* Circle)

/-- Elements of the distinguished product which are `1` on `s`. -/
def productTail (s : Finset ι) : Subgroup (∀ i, U i) :=
  Subgroup.pi (s : Set ι) fun _ ↦ ⊥

end RestrictedProduct
end
