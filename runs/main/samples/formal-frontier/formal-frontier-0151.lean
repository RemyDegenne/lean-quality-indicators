public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

lemma normSequence_exact (M : Rep R G) : (normSequence M).Exact :=
  ComposableArrows.exact_of_iso (homologySequenceIsoNormSequence M)
    (HomologicalComplex.HomologySequence.composableArrows₃_exact
      (tateComplex M) (-1) 0 (by simp))

end FiniteGroupTateCohomology
end
