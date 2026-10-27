@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section FieldRingEquivalence

variable (K : Type u) [hK : Field K]

/-- Integer dimension identifies the tensor-product ring K₀ of a field with
`ℤ`. Its additive equivalence is `finrankEquiv`, and its inverse is integer
multiplication of the regular right-module generator.
See Weibel, *The K-book*, Chapter II, §2. -/
noncomputable def finrankRingEquiv : K0 K ≃+* ℤ :=
  AddEquiv.toRingEquiv (finrankEquiv K) (by
    exact map_mul_of_symm_intCast (finrankEquiv K) fun z ↦
      (finrankEquiv_symm_apply K z).trans (intCast_eq_zsmul K z).symm)

end FieldRingEquivalence
end KTheory.K0
end
