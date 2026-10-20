@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CLStructuralPrefixWriter

open Turing GapCVP.BinaryEncoding

macro "prefixWriterStepTac" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [structuralPrefixWriter, prefixWriterConfiguration,
          prefixWriterPeek, prefixWriterPop, prefixWriterPushBit,
          prefixWriterPushMarker, prefixWriterGoto,
          prefixWriterScanStatement, prefixWriterRestoreStatement,
          prefixWriterMarkerStatement, Turing.haltList,
          Turing.FinTM2.step, Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

/-- The scan phase reverses the input onto scratch and records its length in markers. -/
def prefixWriterScanTrace
    (input scratch markers output : List Bool) :
    EvalsToInTime structuralPrefixWriter.step
      (prefixWriterConfiguration 0 input scratch markers output)
      (some (prefixWriterConfiguration 1 []
        (input.reverse ++ scratch)
        (List.replicate input.length true ++ markers) output))
      (input.length + 1) := by
  induction input generalizing scratch markers with
  | nil =>
      simpa only [FinTM2.step, Fin.isValue, List.reverse_nil, List.nil_append, List.length_nil,
          List.replicate_zero,
          zero_add] using oneStep _ _ (prefixWriterScanFinish scratch markers output)
  | cons bit input ih =>
      have hfirst := oneStep _ _ (prefixWriterScanStep bit input scratch markers output)
      have hrest := ih (bit :: scratch) (true :: markers)
      have hfull := EvalsToInTime.trans structuralPrefixWriter.step _ _ _ _ _ hfirst hrest
      simpa only [FinTM2.step, Fin.isValue, List.reverse_cons, List.append_assoc, List.cons_append,
          List.nil_append,
          List.length_cons, List.replicate_succ', Nat.add_assoc, Nat.reduceAdd] using hfull

end CLStructuralPrefixWriter
end GapCVP
end
end
