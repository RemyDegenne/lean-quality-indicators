@[expose] public section

universe u v

open TensorProduct WithConv

open scoped RingTheory.LinearMap

namespace Coalgebra.IsSkewPrimitiveElem

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]
  {g h a : A}

lemma antipode (ha : IsSkewPrimitiveElem R g h a) :
    IsSkewPrimitiveElem R (HopfAlgebra.antipode R h) (HopfAlgebra.antipode R g)
      (HopfAlgebra.antipode R a) where
  counit_eq_zero := by rw [HopfAlgebra.counit_antipode, ha.counit_eq_zero]
  comul_eq_tmul_add_tmul := by
    rw [HopfAlgebra.comul_antipode, ha.comul_eq_tmul_add_tmul]
    simp only [map_add, _root_.TensorProduct.comm_tmul, _root_.TensorProduct.map_tmul,
      add_comm]

end Coalgebra.IsSkewPrimitiveElem
end
