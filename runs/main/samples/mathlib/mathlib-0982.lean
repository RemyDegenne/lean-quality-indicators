@[expose] public section

open Set

namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y : Set α} {e f : α}

@[simp] lemma closure_inter_ground (M : Matroid α) (X : Set α) :
    M.closure (X ∩ M.E) = M.closure X := by
  simp_rw [closure_def, inter_assoc, inter_self]

end Matroid
end
