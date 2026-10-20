@[expose] public noncomputable section

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

@[simp]
theorem pointSumEquivBlockPoint_sub (x y : Point (n + n)) :
    pointSumEquivBlockPoint n (x - y) =
      pointSumEquivBlockPoint n x - pointSumEquivBlockPoint n y := by
  ext i
  cases i <;> simp

end ViscositySolns
end
