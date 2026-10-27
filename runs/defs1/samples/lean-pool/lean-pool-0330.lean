@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

open SurfaceCellComplex

namespace FiniteCyclicPresentation

variable {Edge : Type} [Fintype Edge]

/-- Pull a typed one-face pairing forward to the enumerated finite-cyclic word. -/
noncomputable def ofOneFaceWordComapPairing
    (word : List (SignedDart Edge))
    (valid : (ofOneFaceWord word).IsSurfaceValid)
    (pairing : (oneFacePresentation Edge word).BoundaryPairing) :
    (ofOneFaceWord word).BoundaryPairing := by
  let source := (ofOneFaceWordOccurrenceEquiv word).symm pairing.source
  let target := (ofOneFaceWordOccurrenceEquiv word).symm pairing.target
  have hne : source ≠ target :=
    (ofOneFaceWordOccurrenceEquiv word).symm.injective.ne
      pairing.source_ne_target
  have hcompatible :
      match pairing.direction with
      | .same => target.dart = source.dart
      | .opposite => target.dart = source.dart.flip := by
    cases hdirection : pairing.direction with
    | same =>
        have hp :
            (oneFacePresentation Edge word).occurrenceDart pairing.target =
              (oneFacePresentation Edge word).occurrenceDart pairing.source := by
          simpa only [hdirection] using pairing.compatible
        calc
          target.dart =
              SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.target) :=
            (ofOneFaceWordComapOccurrence_dart word pairing.target).symm
          _ = SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source) :=
            congrArg (SignedDart.mapEquiv (Fintype.equivFin Edge)) hp
          _ = source.dart :=
            ofOneFaceWordComapOccurrence_dart word pairing.source
    | opposite =>
        have hp :
            (oneFacePresentation Edge word).occurrenceDart pairing.target =
              (oneFacePresentation Edge word).inv
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source) := by
          simpa only [hdirection] using pairing.compatible
        change
          (oneFacePresentation Edge word).occurrenceDart pairing.target =
            ((oneFacePresentation Edge word).occurrenceDart
              pairing.source).flip at hp
        calc
          target.dart =
              SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.target) :=
            (ofOneFaceWordComapOccurrence_dart word pairing.target).symm
          _ = SignedDart.mapEquiv (Fintype.equivFin Edge)
                ((oneFacePresentation Edge word).occurrenceDart
                  pairing.source).flip := by
            exact congrArg
              (SignedDart.mapEquiv (Fintype.equivFin Edge)) hp
          _ = source.dart.flip := by
            rw [SignedDart.mapEquiv_flip,
              ofOneFaceWordComapOccurrence_dart]
  have hedge : target.edge = source.edge := by
    cases hdirection : pairing.direction with
    | same =>
        have hsame : target.dart = source.dart := by
          simpa only [hdirection] using hcompatible
        exact congrArg edgeOfDart hsame
    | opposite =>
        have hopp : target.dart = source.dart.flip := by
          simpa only [hdirection] using hcompatible
        simpa only [BoundaryOccurrence.edge, edgeOfDart_flip] using
          congrArg edgeOfDart hopp
  have hsourceBoundary :
      ¬(ofOneFaceWord word).IsBoundaryEdge source.edge :=
    valid.not_isBoundaryEdge_of_distinct_occurrences source target hne hedge
  have htargetBoundary :
      ¬(ofOneFaceWord word).IsBoundaryEdge target.edge := by
    rw [hedge]
    exact hsourceBoundary
  exact
    { source := source
      target := target
      source_ne_target := hne
      source_not_boundary := hsourceBoundary
      target_not_boundary := htargetBoundary
      direction := pairing.direction
      compatible := hcompatible }

end FiniteCyclicPresentation
end LeanEval.Topology.ClassificationOfSurfaces
end
