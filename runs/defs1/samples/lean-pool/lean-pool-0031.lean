@[expose] public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFUnaryPairIndexTotalCert

open Computability Turing GapCVP.CNFUnaryPairIndexTM

/-- GapCVP reduction support. -/
def unaryPairFirstTrace
    (count : ℕ)
    (tail first second matchedFirst matchedSecond
      base outer output scratch : List Bool) :
    EvalsToInTime actualUnaryPairIndexMachine.step (unaryPairConfiguration 0
        (List.replicate count true ++ false :: tail)
        first second matchedFirst matchedSecond
        base outer output scratch)
      (some (unaryPairConfiguration 1 tail
        (List.replicate count true ++ first)
        second matchedFirst matchedSecond
        base outer output scratch))
      (count + 1) := by
  induction count generalizing first with
  | zero =>
      simpa only [FinTM2.step, Fin.isValue, List.replicate_zero, List.nil_append, zero_add] using
          oneStep _ _ (unaryPair_first_false tail first second matchedFirst matchedSecond base
              outer output scratch)
  | succ count ih =>
      have hfirst := oneStep _ _ (unaryPair_first_true
          (List.replicate count true ++ false :: tail)
          first second matchedFirst matchedSecond
          base outer output scratch)
      have hrest := ih (true :: first)
      simpa only [FinTM2.step, Fin.isValue, List.replicate_succ, List.cons_append, Nat.add_comm,
          Nat.add_left_comm,
          Nat.reduceAdd, SourceStructuralDecoder.replicate_true_append_cons] using
          EvalsToInTime.trans actualUnaryPairIndexMachine.step _ _ _ _ _ hfirst hrest

end CNFUnaryPairIndexTotalCert
end GapCVP
end
end
