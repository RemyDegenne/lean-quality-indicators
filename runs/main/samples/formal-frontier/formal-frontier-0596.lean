@[expose] public section

open Set Function

set_option linter.style.haveILetI false

universe u

namespace ProfiniteGrp

theorem subgroup_eq_powerImage_of_isOpen (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    H = (powerImage G hG H.index : Subgroup G) :=
  openSubgroup_eq_powerImage G hG ⟨H, hH⟩

end ProfiniteGrp
end
