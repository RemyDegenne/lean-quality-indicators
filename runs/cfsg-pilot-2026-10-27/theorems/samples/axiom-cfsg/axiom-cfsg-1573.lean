public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

open CFSG.FeitThompson.Prep03

attribute [local instance] CFSG.FeitThompson.subgroupFintype

variable {G : Type*} [Group G]

theorem mem_classFun_of_mem_classFun_top {f : ↥(⊤ : Subgroup G) → ℂ}
    (hf : f ∈ classFun ↥(⊤ : Subgroup G)) :
    (fun x : G => f ⟨x, Subgroup.mem_top x⟩) ∈ classFun G := by
  refine mem_classFun.2 fun x y hxy => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  exact mem_classFun.1 hf _ _
    (isConj_iff.2 ⟨⟨c, Subgroup.mem_top c⟩, Subtype.ext (by simpa using hc)⟩)

end CFSG.FeitThompson
end
