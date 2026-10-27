public section

namespace CFSG.Quasithin.F53Mod

open Equiv

variable {n : ℕ}

theorem Model.Iso.index_fixW_eq {M N : Model n} (e : M.Iso N) (B : Subgroup (Perm (Fin n))) :
    (fixW N B).index = (fixW M B).index := by
  rw [e.fixW_eq B]
  exact Subgroup.index_map_equiv _ e.toMulEquiv

end CFSG.Quasithin.F53Mod
end
