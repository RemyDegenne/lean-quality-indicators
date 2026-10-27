public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] instFintypeRange Subgroup.fintypeQuotientOfFiniteIndex

/-- **Corestriction between the Tate cohomology groups of finite normal layers, in every integer
degree.** Positive degrees use ordinary cohomological corestriction, degrees zero and minus one
use the low-degree norm descriptions, and lower degrees use group-homological corestriction. -/
def tateCor (T : LayerRestriction small big) (F : Formation G) :
    (r : ℤ) → small.TateH F r ⟶ big.TateH F r
  | .ofNat 0 =>
      (T.tateRangeIso F 0).hom ≫
        TauCeti.TateCohomology.H0Cor (big.rep F) T.galHom.range
  | .ofNat (n + 1) =>
      (small.tateHIsoH F (n + 1)).hom ≫ T.cohomologyCor F (n + 1) ≫
        (big.tateHIsoH F (n + 1)).inv
  | .negSucc 0 =>
      (T.tateRangeIso F (-1)).hom ≫
        TauCeti.TateCohomology.HNegOneCor (big.rep F) T.galHom.range
  | .negSucc (n + 1) =>
      (T.tateRangeIso F (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (big.rep F) T.galHom.range.subtype (n + 1)

end TauCeti.ClassFieldTheory.LayerRestriction
end
