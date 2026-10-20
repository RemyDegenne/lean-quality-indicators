@[expose] public section

variable {A : Type*} [CStarAlgebra A]

open scoped ComplexStarModule

open Complex

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- For `a` selfadjoint with `‖a‖ ≤ 1`, this is the unitary `a + I • √(1 - a ^ 2)`. -/
@[simps]
noncomputable def selfAdjoint.unitarySelfAddISMul (a : selfAdjoint A) (ha_norm : ‖a‖ ≤ 1) :
    unitary A :=
  ⟨(a : A) + I • CFC.sqrt (1 - a ^ 2 : A), a.2.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary _ ha_norm⟩

end Ordered
end
