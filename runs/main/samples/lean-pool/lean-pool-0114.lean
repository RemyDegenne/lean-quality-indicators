@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace

open Complex Matrix Finset

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker

open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactReverseBobMarkedHistoryContext_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_history :
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome'))
    (same_question :
      outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val) :
    exactReverseBobMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome' := by
  have hmask := exactReverseBobMaskedProjection_eq_of_history
    (X := X) (Y := Y) (A := A) (B := B)
    D default (seed, outcome) (seed, outcome')
    same_history same_question
  have hflag := exactConditionedAnswerFlag_eq_of_history
    G n S D (seed, outcome) (seed, outcome') same_history
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide seed) (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide seed) (seed, outcome')).1 := by
    have h := congrArg
      (fun t :
        ExactReverseBobFixedInformation X Y D
          (exactReverseRightSide seed) ×
            (Fin (exactReverseRightSide seed).card → X) =>
        t.1) hmask
    simpa only [finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseRightSide seed) (seed, outcome))).2 =
      (finitePrefixMask default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseRightSide seed) (seed, outcome'))).2 := by
    exact congrArg
      (fun t :
        ExactReverseBobFixedInformation X Y D
          (exactReverseRightSide seed) ×
            (Fin (exactReverseRightSide seed).card → X) =>
        t.2) hmask
  unfold exactReverseBobMarkedHistoryContext
  dsimp
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · exact hflag
  · exact hprefix

end
end QuantumParallelRepetition
end
end
