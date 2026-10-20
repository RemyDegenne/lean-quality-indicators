@[expose] public section

universe u

variable {R : Type u} [Ring R] {x y : R}

namespace LinearEquiv

@[simp] theorem rightRegularEquivProdOfMulEqOne_apply_snd_coe
    (hxy : x * y = 1) (r : R) :
    ((rightRegularEquivProdOfMulEqOne hxy r).2 : R) = (1 - y * x) * r := by
  rfl

end LinearEquiv
end
