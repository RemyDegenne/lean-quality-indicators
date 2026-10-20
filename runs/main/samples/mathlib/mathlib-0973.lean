@[expose] public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] (W : ℤ → R) {F : Type*} [FunLike F R S]
  [RingHomClass F R S] (f : F)

namespace IsEllipticNet

variable {W} in
@[simp]
lemma atomRel_same₁₄ (neg : W.Odd) (a b c : ℤ) : atomRel W a b c a = W a * W 0 * atom W b c := by
  grind only [atomRel, atom_same, neg_atom]

end IsEllipticNet
end
