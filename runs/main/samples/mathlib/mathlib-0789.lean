public section

variable {F α β : Type*}

open Rat

variable [FunLike F α β]

namespace MonoidWithZeroHomClass

variable {M₀ : Type*} [MonoidWithZero M₀]

section NNRat

variable [FunLike F ℚ≥0 M₀] [MonoidWithZeroHomClass F ℚ≥0 M₀] {f g : F}

lemma ext_nnrat' (h : ∀ n : ℕ, f n = g n) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, eq_on_inv₀ f g]
    apply h

end NNRat
end MonoidWithZeroHomClass
end
