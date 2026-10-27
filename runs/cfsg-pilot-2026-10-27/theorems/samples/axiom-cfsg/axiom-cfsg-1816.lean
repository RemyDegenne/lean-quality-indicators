public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_case1_of_no_preUniqueness (hS : GLStanding G 4 3) {B M₀ : Subgroup G}
    (hB : IsBOneMax 3 B) (h63 : Prop63Out B M₀) (h67 : Prop67Out B) (h68 : Prop68Out B)
    (hU : UniqComp B) (h75 : Lemma75Stmt B) (h76 : Lemma76Stmt B)
    (hno : ¬ ∃ M : Subgroup G, IsPreUniquenessSubgroup 3 B M) : ¬ Case1Hyp B := fun hC =>
  hno (exists_preUniqueness_of_case1 hS hB h63 h67 h68 hU h75 h76 hC
    (exists_isHSet_of_no_preUniqueness hS hB h63 h67 hno))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
end
