public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp83

variable {V H T : Subgroup G}

theorem conjSubgroup_kGen (h : Hyp83 V H T) (hOmH : ∀ W ∈ omegaSet V H (eSub V H T), W ≤ H)
    {x : G} (hx : x ∈ H) :
    conjSubgroup (kGen V H T) x = kOrbSub V H (eSub V H T) (conjSubgroup V x) := by
  rw [kGen_eq_kOrbSub]
  exact conjSubgroup_kOrbSub h.eSub_le_H h.eSub_subgroupOf_normal hOmH hx

end Hyp83
end CFSG.LocalAnalysis.WeakClosure81
end
