@[expose] public section

noncomputable section

open Affine

open Set

open scoped Pointwise

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

open AffineSubspace

section

variable {s : Set P}

theorem affineSpan_nonempty : (affineSpan k s : Set P).Nonempty ↔ s.Nonempty :=
  spanPoints_nonempty k s

end
end AffineSpace'
end
end
