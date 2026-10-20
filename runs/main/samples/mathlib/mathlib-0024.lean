@[expose] public section

open Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

namespace Set

open scoped Interval

section LinearOrder

variable [LinearOrder α]

section Lattice

variable [Lattice β] {f : α → β} {a b : α}

lemma _root_.AntitoneOn.image_uIcc_subset (hf : AntitoneOn f (uIcc a b)) :
    f '' uIcc a b ⊆ uIcc (f a) (f b) := hf.mapsTo_uIcc.image_subset

end Lattice
end LinearOrder
end Set
end
