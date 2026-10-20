public section

set_option warningAsError true

open Filter Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}

variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]

variable [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))

variable (e : ∀ i, X i →* Y i →* Circle)

@[simp]
theorem toPontryaginDual_apply
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (y : Πʳ i, [Y i, V i]) (x : Πʳ i, [X i, U i]) :
    toPontryaginDual U V e horth hUopen hVopen he y x = pairing U V e x y :=
  rfl

end RestrictedProduct
end
