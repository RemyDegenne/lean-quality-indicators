public section

open Polynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section preΨ

lemma preΨ_ne_zero [Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0) : W.preΨ n ≠ 0 := by
  induction n using Int.negInduction with
  | nat n => simpa only [preΨ_ofNat] using W.preΨ'_ne_zero <| by exact_mod_cast h
  | neg ih n => simpa only [preΨ_neg, neg_ne_zero]
        using ih n <| neg_ne_zero.mp <| by exact_mod_cast h

end preΨ
end WeierstrassCurve
end
