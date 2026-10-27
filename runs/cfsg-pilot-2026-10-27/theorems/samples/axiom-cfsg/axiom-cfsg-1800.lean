public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix

open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

namespace S2341Frame

theorem W_le_pCore {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    X.W ≤ conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h := by
  rw [X.hW]
  exact E3.conjSubgroup_mono_left X.h
    ((uc22p22v_le_conjClosure D.M c.V).trans (c.E_le_pCoreOf_M h39 h1930))

end S2341Frame
end Ctx23L
end CFSG.LocalAnalysis.UniquenessCase.UC22
end
