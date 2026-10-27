public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.Open (IsElemAbelian)

section Core

variable {G : Type} [Group G] [Finite G] {K R T : Subgroup G} {g : G}

theorem analysis_core (B : Branches G) (cfg : NAConfig G K R T g) :
    ¬ IsElemAbelian 2 T ∧ ¬ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
  by_cases hel : IsElemAbelian 2 T
  · exfalso
    rcases cfg.caseII hel with h4 | ⟨H, h5⟩
    · exact B.c2 cfg h4
    · by_cases hH : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (H : Set G)
      · exact B.c3 cfg h5 hH
      · exact B.c4 cfg h5 hH
  · exact ⟨hel, fun hN => caseI_normal_false cfg (cfg.caseI hel) hN⟩

end Core
end CFSG.CGT.PushingUpLit.SolKNA
end
