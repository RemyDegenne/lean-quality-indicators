public section

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

section Pair

variable [NeZero n]

lemma posDetInt_le_commensurator :
    posDetInt n ≤ (commensurator (SLnZ n)).toSubmonoid := fun _ hg ↦
  (Subgroup.mem_toSubmonoid _ _).mpr
    (mem_commensurator_of_hasIntEntries n hg.1)

end Pair
end HeckeRing.GLn
end
