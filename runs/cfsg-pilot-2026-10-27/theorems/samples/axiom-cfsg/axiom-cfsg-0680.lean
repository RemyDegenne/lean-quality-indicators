public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

namespace CaseTwoTransitive

variable {G : Type} [Group G] [Finite G] {c : Ctx812E G} (t : CaseTwoTransitive c)

section Full

variable {G : Type} [Group G] [Finite G] {c : Ctx812 G} (t : CaseTwoTransitive c.toCtx812E)

theorem centralizer_Z_le (hK : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326.K326P2S)
    {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) :
    Subgroup.centralizer (t.Z : Set G) ≤ c.S.M :=
  t.centralizer_Z_le_of_pairNormalizerLe hK hp h76 (t.pairNormalizerLe hp h76)

end Full
end CaseTwoTransitive
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
end
