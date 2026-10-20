@[expose] public section

variable (R : Type*) {V V' P P' : Type*}

open AffineEquiv AffineMap Module

section OrderedRing

variable [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

@[simp]
theorem affineSegment_vadd_const_image (x y : V) (p : P) :
    (· +ᵥ p) '' affineSegment R x y = affineSegment R (x +ᵥ p) (y +ᵥ p) :=
  affineSegment_image (AffineEquiv.vaddConst R p : V →ᵃ[R] P) x y

end OrderedRing
end
