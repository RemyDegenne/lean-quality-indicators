@[expose] public section

namespace CategoryTheory

open Set Groupoid

universe u v

variable {C : Type u} [Groupoid C]

namespace Subgroupoid

variable (S : Subgroupoid C)

/-- The subgroup of the vertex group at `c` given by the subgroupoid -/
def vertexSubgroup {c : C} (hc : c ∈ S.objs) : Subgroup (c ⟶ c) where
  carrier := S.arrows c c
  mul_mem' hf hg := S.mul hf hg
  one_mem' := id_mem_of_nonempty_isotropy _ _ hc
  inv_mem' hf := S.inv hf

end Subgroupoid
end CategoryTheory
end
