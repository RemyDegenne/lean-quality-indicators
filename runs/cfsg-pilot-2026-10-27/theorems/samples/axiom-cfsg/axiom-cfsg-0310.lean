public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris
  CFSG.Assembly.LowTwoRank CFSG.SectionRank

section Generic

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf_of_le {X Y M : Subgroup G} (hM : CFSG.Open.IsComponentOf M X)
    (hYX : Y ≤ X) (hMY : M ≤ Y) : CFSG.IsComponent (M.subgroupOf Y) := by
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMY).symm
    (isQuasisimple_of_open hM.2.2), ?_⟩
  have h := Quasithin.A3.subnormal_comap Y.subtype hM.2.1
  rw [show X.comap Y.subtype = ⊤ from (Subgroup.eq_top_iff' _).2 fun y => hYX y.2] at h
  exact mathlibSubnormal_of_open_top h

end Generic
end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
end
