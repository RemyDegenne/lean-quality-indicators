@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [instance] FiniteDiscretePresentation.smallCategory
  FiniteDiscretePresentation.cofiltered

theorem finiteDiscretePresentation_iff_compact_totallyDisconnected (X : Type u)
    [TopologicalSpace X] [T2Space X] :
    Nonempty (FiniteDiscretePresentation X) ↔
      CompactSpace X ∧ TotallyDisconnectedSpace X := by
  constructor
  · rintro ⟨P⟩
    exact ⟨Homeomorph.compactSpace P.equiv.symm,
      Homeomorph.totallyDisconnectedSpace P.equiv.symm⟩
  · rintro ⟨hcompact, hdisconnected⟩
    let : CompactSpace X := hcompact
    let : TotallyDisconnectedSpace X := hdisconnected
    exact ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of X)⟩

end
