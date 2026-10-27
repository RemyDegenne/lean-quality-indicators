public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE

section Commute

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem noFrobeniusInner_of_anyKind (hAF : AnyKindNoFrobenius) (hbig : ThreeBigComponents)
    (S : LangSetup τ L 3) (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) (hq4' : S.D.q ≠ 4 ∨ SimplyLacedTag τ)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2) :
    NoFrobeniusInner S D₁ :=
  hAF τ L 3 S hτ hq4' D₁ hD₁E (hasBigAnyComponent_of_threeBig hbig S hq4 hD₁E hD₁c)

end Commute
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
