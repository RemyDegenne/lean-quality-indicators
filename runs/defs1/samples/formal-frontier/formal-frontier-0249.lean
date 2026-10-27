public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The concrete norm sequence is isomorphic to the canonical homology sequence
of the Tate complex. -/
noncomputable def homologySequenceIsoNormSequence (M : Rep R G) :
    HomologicalComplex.HomologySequence.composableArrows₃ (tateComplex M) (-1) 0 ≅
      normSequence M :=
  ComposableArrows.isoMk₃ (Iso.refl _) (tateOpcyclesIsoNegOne M)
    (tateCyclesIsoZero M) (Iso.refl _)
    (by
      dsimp [-Fin.reduceFinMk, HomologicalComplex.HomologySequence.composableArrows₃,
        normSequence]
      simp)
    (by
      dsimp [-Fin.reduceFinMk, HomologicalComplex.HomologySequence.composableArrows₃,
        normSequence]
      rw [← tateNormFromCoinvariants_eq]
      simp [tateNormFromCoinvariants])
    (by
      dsimp [-Fin.reduceFinMk, HomologicalComplex.HomologySequence.composableArrows₃,
        normSequence]
      simp)

end FiniteGroupTateCohomology
end
