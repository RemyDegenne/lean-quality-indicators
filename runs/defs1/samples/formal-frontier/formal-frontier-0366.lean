public section

set_option warningAsError true

open Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}

variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]

variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))

variable (e : ∀ i, X i →* Y i →* Circle)

/-- The left annihilator of a subgroup under a multiplicative bicharacter. -/
@[expose] noncomputable def leftAnnihilator {X Y : Type*} [CommGroup X] [CommGroup Y]
    (V : Subgroup Y) (e : X →* Y →* Circle) : Subgroup X :=
  rightAnnihilator V (rightCharacter e)

end RestrictedProduct
end
