public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Ctx

variable {G : Type} [Group G] {a z₀ b₀ z u x b c : G}
  {φ : Subgroup.centralizer ({b} : Set G) →* B}

namespace TableVICtx

theorem orderOf_c (C : TableVICtx a z₀ b₀ z u x b φ) (hc : c ∈ tableVISet a x b) :
    orderOf c = 2 :=
  (orderOf_eq_of_isConj hc.1.1).symm.trans C.two.orderOf_a

end TableVICtx
end Ctx
end CFSG.Monster.GMS
end
