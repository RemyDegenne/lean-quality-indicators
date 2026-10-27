public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G] [Finite G]

namespace NormPair

variable {A R T : Subgroup G} {g : G} {n : ℕ} (np : NormPair A R T g n)

include np

omit [Finite G] in
theorem swap_ψB (y : normalizer (rightConjugate A g⁻¹ : Set G)) :
    np.swap.ψB y = np.ψA (conjN A g⁻¹ y) :=
  rfl

end NormPair
end CFSG.ComponentClassification.RankTwoAlt
end
