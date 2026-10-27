public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The four-term norm sequence in exceptional Tate degrees. -/
@[expose]
noncomputable def normSequence (M : Rep R G) : ComposableArrows (ModuleCat R) 3 :=
  ComposableArrows.mk₃
    ((tateComplex M).homologyι (-1) ≫ (tateOpcyclesIsoNegOne M).hom)
    (normFromCoinvariants M)
    ((tateCyclesIsoZero M).inv ≫ (tateComplex M).homologyπ 0)

end FiniteGroupTateCohomology
end
