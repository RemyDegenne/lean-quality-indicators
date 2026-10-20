public noncomputable section

open CategoryTheory Rep Representation

namespace TauCeti.ClassFieldTheory.LayerRestriction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {small big : NormalLayer G}

attribute [local instance] instFintypeRange Subgroup.fintypeQuotientOfFiniteIndex

@[simp]
theorem tateCor_negSucc_succ (T : LayerRestriction small big) (F : Formation G) (n : ℕ) :
    T.tateCor F (Int.negSucc (n + 1)) =
      (T.tateRangeIso F (Int.negSucc (n + 1))).hom ≫
        TauCeti.TateCohomology.negSuccCor
          (big.rep F) T.galHom.range.subtype (n + 1) :=
  (rfl)

end TauCeti.ClassFieldTheory.LayerRestriction
end
