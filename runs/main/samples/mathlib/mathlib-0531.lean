@[expose] public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] (W : ℤ → R) {F : Type*} [FunLike F R S]
  [RingHomClass F R S] (f : F)

namespace IsEllipticNet

lemma rel_odd (m : ℤ) : rel W (m + 1) m 1 0 =
    W (2 * m + 1) * W 1 ^ 3 - W (m + 2) * W m ^ 3 + W (m - 1) * W (m + 1) ^ 3 := by
  grind only [rel]

end IsEllipticNet
end
