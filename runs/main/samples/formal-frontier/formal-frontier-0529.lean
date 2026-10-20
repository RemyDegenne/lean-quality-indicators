@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Coalgebra

section CommRing

variable (R : Type u) (C : Type v)

variable [CommRing R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [FaithfulSMul R C]

theorem counit_surjective_of_faithfulSMul_of_fg
    (hfg : (LinearMap.range (counit (R := R) (A := C)) : Ideal R).FG) :
    Function.Surjective (counit (R := R) (A := C)) :=
  LinearMap.range_eq_top.mp (counit_range_eq_top_of_faithfulSMul_of_fg R C hfg)

end CommRing
end Coalgebra
end
