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

/-- The continuous character of the first restricted product determined by an element of the
second restricted product. -/
@[expose] noncomputable def pairingCharacter
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2)
    (y : Πʳ i, [Y i, V i]) : PontryaginDual (Πʳ i, [X i, U i]) :=
  ContinuousMonoidHom.mk (pairingMonoidHom U V e horth y) <|
    (continuous_pairing U V e horth hUopen hVopen he).comp (continuous_id.prodMk continuous_const)

end RestrictedProduct
end
