open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional

open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)

open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)

open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)

open CFSG.ABGLocalTools (IsSylowOf)

open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open scoped commutatorElement Pointwise MatrixGroups

namespace CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux

open CFSG.LocalAnalysis.EvenBN.TrialityD4 (mem_normalizer_inf_D4 mem_normalizer_centralizer_D4)

namespace Ctx

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] {f : ℕ} {t wb : G}
  {W Y M N P F₅ A Λ : Subgroup G} (C : Ctx K f t wb W Y M N P F₅ A Λ)

include C

theorem A_NM : A ≤ normalizer (M : Set G) := C.A_N.trans C.N_M

end Ctx
end CFSG.LocalAnalysis.EvenBN.G2.ProductN2Aux
