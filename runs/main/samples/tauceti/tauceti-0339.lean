public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

@[simp]
theorem referenceSubgroup_four_two :
    referenceSubgroup 4 ⟨2, by simp [numTransitiveGroups]⟩ =
      Subgroup.closure {finRotate 4, swap 0 2} := by
  simp [referenceSubgroup, referenceSubgroup4]

end TauCeti
end
