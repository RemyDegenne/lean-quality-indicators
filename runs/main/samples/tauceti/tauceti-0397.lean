public section

noncomputable section

open Module

namespace Orientation

variable {R E F : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  {m n : ℕ}

variable [Module.Free R E] [Module.Finite R E]
  [Module.Free R F] [Module.Finite R F]

@[simp]
theorem prod_neg_right (o : Orientation R E (Fin m)) (p : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    prod o (-p) hm hn = -prod o p hm hn := by
  let b := Module.finBasisOfFinrankEq R E hm
  let c := Module.finBasisOfFinrankEq R F hn
  rw [prod_eq_rayOfNeZero _ _ hm hn b c, prod_eq_rayOfNeZero _ _ hm hn b c]
  simp only [signBasis_neg, Units.val_neg, Int.cast_neg, mul_neg, neg_rayOfNeZero]
  congr 1
  module

end Orientation
end
end
