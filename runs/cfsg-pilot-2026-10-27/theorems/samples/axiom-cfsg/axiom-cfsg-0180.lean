public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

open scoped commutatorElement IsMulCommutative

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem Q_le_H49 {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) : Q ≤ H :=
  h.Q_eq.le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
end
