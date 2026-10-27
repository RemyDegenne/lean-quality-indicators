public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix

variable {K : Type} [Field K]

theorem planeBlock_one (i : Fin 3) : planeBlock K i (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  unfold planeBlock
  rw [Function.update_eq_self_iff.mpr rfl]
  exact blockMat_one

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
end
