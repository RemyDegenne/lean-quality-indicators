public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Local

variable {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}

theorem mem_stabilizerOf_iff_smul {k : GLV V} :
    k ∈ stabilizerOf K U ↔ k ∈ K ∧ k • subToSubgroup U = subToSubgroup U := by
  rw [← subToSubgroup_conjSub]
  exact and_congr_right fun _ => subToSubgroup_inj.symm

end Local
end G11
end CFSG.Quasithin
end
