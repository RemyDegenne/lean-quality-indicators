@[expose] public section

open Set Function

set_option linter.style.haveILetI false

universe u

namespace ProfiniteGrp

theorem openSubgroup_eq_of_index_eq (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (H K : OpenSubgroup G)
    (hindex : (H : Subgroup G).index = (K : Subgroup G).index) : H = K := by
  apply OpenSubgroup.toSubgroup_injective
  rw [openSubgroup_eq_powerImage G hG H,
    openSubgroup_eq_powerImage G hG K, hindex]

end ProfiniteGrp
end
