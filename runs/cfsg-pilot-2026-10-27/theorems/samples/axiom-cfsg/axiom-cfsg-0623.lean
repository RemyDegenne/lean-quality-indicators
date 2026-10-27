public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Matrix

theorem mulN_eq (A B : List ℕ) : toMat (mulN A B) = toMat A * toMat B := by
  ext r j
  have h : (B.map (mvN A)).getD j.val 0 = mvN A (B.getD j.val 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases B[j.val]? with
    | none => simp [mvN_zero]
    | some x => simp
  simp only [toMat, mulN, Matrix.of_apply, h, mvN_eq]
  rfl

end CFSG.EvenSporadicStandard.Wong77.Cls
end
