namespace OAI

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

namespace Program

variable {Input : Type*}

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

end Program
end MatrixMultiplication.Foundation.Arithmetic
end
end OAI
