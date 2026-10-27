public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Setting15419

variable (s : Setting15419 G T)

theorem pCoreOf_X_le_centralizer (hyp : MultipleCentralizerHypothesis G T)
    (h12 : Stmt15412 G T) :
    pCoreOf 2 s.X ≤ Subgroup.centralizer (VZ T s.M₁ : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((s.VZ_le_centerOf hyp hv).2 n (s.pCoreOf_X_le h12 hn)).symm

end Setting15419
end CFSG.Quasithin.EmptyFaithfulMultiple
end
