public section

set_option warningAsError true

open Filter Function Set Topology

open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {X Y : ι → Type*}

variable [∀ i, CommGroup (X i)] [∀ i, CommGroup (Y i)]

variable (U : ∀ i, Subgroup (X i)) (V : ∀ i, Subgroup (Y i))

variable (e : ∀ i, X i →* Y i →* Circle)

variable [∀ i, TopologicalSpace (X i)]

/-- The coordinate recovered from a global character through an explicitly bijective local
character map. -/
noncomputable def reconstructedCoordinate
    (hperfect : ∀ i, Function.Bijective (rightCharacter (e i)))
    (χ : PontryaginDual (Πʳ i, [X i, U i])) (i : ι) : Y i :=
  (MulEquiv.ofBijective (rightCharacter (e i)) (hperfect i)).symm (coordinateCharacter U χ i)

end RestrictedProduct
end
