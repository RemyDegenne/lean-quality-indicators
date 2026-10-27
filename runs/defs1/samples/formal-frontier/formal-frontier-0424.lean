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

/-- The canonical continuous homomorphism from the second restricted product to the Pontryagin
dual of the first. This construction assumes orthogonality and continuity, but not perfectness or
exact-annihilator hypotheses. -/
@[expose] noncomputable def toPontryaginDual
    (horth : ∀ i (x : X i), x ∈ U i → ∀ y : Y i, y ∈ V i → e i x y = 1)
    (hUopen : ∀ i, IsOpen (U i : Set (X i))) (hVopen : ∀ i, IsOpen (V i : Set (Y i)))
    (he : ∀ i, Continuous fun p : X i × Y i ↦ e i p.1 p.2) :
    (Πʳ i, [Y i, V i]) →ₜ* PontryaginDual (Πʳ i, [X i, U i]) := by
  refine ContinuousMonoidHom.mk
    { toFun := pairingCharacter U V e horth hUopen hVopen he
      map_one' := ContinuousMonoidHom.ext fun x ↦ pairing_one_right U V e x
      map_mul' := fun y y' ↦
        ContinuousMonoidHom.ext fun x ↦ pairing_mul_right U V e horth x y y' } ?_
  apply ContinuousMonoidHom.continuous_of_continuous_uncurry
  exact (continuous_pairing U V e horth hUopen hVopen he).comp
    (continuous_snd.prodMk continuous_fst)

end RestrictedProduct
end
