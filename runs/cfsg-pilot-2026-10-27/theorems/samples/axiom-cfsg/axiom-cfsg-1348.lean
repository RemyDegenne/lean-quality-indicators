public section

namespace CFSG.GroupTheory.PlaneAction

open Finset

theorem orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

end CFSG.GroupTheory.PlaneAction
end
