public section

namespace Subgroup

variable {G : Type*} [Group G] (N : Subgroup G)

variable {N}

@[simp]
theorem ker_indexTwoCharacter (hN : N.index = 2) : (N.indexTwoCharacter hN).ker = N :=
  Subgroup.ext fun _ => (MonoidHom.mem_ker).trans (indexTwoCharacter_eq_one_iff hN)

end Subgroup
end
