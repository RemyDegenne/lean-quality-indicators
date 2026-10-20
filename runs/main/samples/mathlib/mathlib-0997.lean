@[expose] public section

universe u v w

open Module Polynomial nonZeroDivisors

section

variable {K L R S A : Type*}

section Ring

section Field

variable [Field K] [Field L] [Ring A]

variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

variable (L)

@[stacks 09GF "part two"]
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

end Field
end Ring
end
end
