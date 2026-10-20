public section

open scoped TensorProduct

namespace TauCeti

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

theorem mul'_rTensor_mulLeft (a : A) (t : A ⊗[R] A) :
    LinearMap.mul' R A ((LinearMap.mulLeft R a).rTensor A t) =
      a * LinearMap.mul' R A t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

end LinearMap
end TauCeti
end
