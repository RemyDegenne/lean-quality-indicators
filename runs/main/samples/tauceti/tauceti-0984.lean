public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

section HighestWeight

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n]

variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule (Matrix n n R) M]

variable {mu nu : n → R} {v : M}

theorem IsGlHighestWeightVector.weight_eq [IsCancelMulZero R] [Module.IsTorsionFree R M]
    (hv : IsGlHighestWeightVector mu v) (hv' : IsGlHighestWeightVector nu v) : mu = nu := by
  funext i
  have hsmul : mu i • v = nu i • v := by
    rw [← hv.lie_single_self_eq_smul i, hv'.lie_single_self_eq_smul i]
  exact smul_left_injective R hv.ne_zero hsmul

end HighestWeight
end TauCeti
end
