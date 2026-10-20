@[expose] public section

namespace Stafford38.EulerSurjectivity

variable {A : Type*} [Ring A]

/-- Right multiplication on the quotient. -/
def rightMul (I : RightIdeal A) (a : A) (q : RightQuotient I) :
    RightQuotient I :=
  MulOpposite.op a • q

end Stafford38.EulerSurjectivity
end
