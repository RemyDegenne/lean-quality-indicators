@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/-- Pointwise sum of two operators. -/
def addOperator (F G : Operator n) : Operator n :=
  fun x r p X => F x r p X + G x r p X

end ViscositySolns
end
