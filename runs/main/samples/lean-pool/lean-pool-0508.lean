@[expose] public section

namespace BGS.Markoff

open scoped ArithmeticFunction.Moebius BigOperators

open Filter

noncomputable section

variable {G H T : Type*} [CommGroup G] [CommGroup H]

section SplitApplication

theorem splitPrimitiveTraceSolutions_card_error_le_of_weilBoundAssumption
    (p : ℕ) [Fact p.Prime]
    (coefficient : ℕ) (hWeil : WeightedSplitTraceWeilBoundAssumption coefficient)
    (alpha beta : ZMod p) (orbitExponent : ℕ)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hnondegenerate : alpha * beta ≠ 1)
    (horbitPositive : 0 < orbitExponent)
    (horbitChar : (orbitExponent : ZMod p) ≠ 0)
    (horbitDvd : orbitExponent ∣ Nat.card (ZMod p)ˣ) :
    |((splitPrimitiveTraceSolutions p alpha beta orbitExponent).card : ℝ) -
        primitiveTraceMoebiusMainTerm
          (Nat.card (ZMod p)ˣ) p orbitExponent| ≤
      ((Nat.card (ZMod p)ˣ).divisors.card : ℝ) *
        ((coefficient : ℝ) * Real.sqrt (p : ℝ)) := by
  have hRange : ∀ d : ℕ, d ∣ Nat.card (ZMod p)ˣ → 0 < d →
      |(Nat.card (powerTraceRangeSolutions
          (weightedSplitTorusTrace alpha beta)
          (splitTorusTrace : (ZMod p)ˣ → ZMod p) orbitExponent d) : ℝ) -
        (p : ℝ) / ((d : ℝ) * (orbitExponent : ℝ))| ≤
          (coefficient : ℝ) * Real.sqrt (p : ℝ) := by
    intro d hdvd hd
    have hestimate :=
      splitTracePowerRangeSolutions_count_error_le_of_weilBoundAssumption
        (ZMod p) coefficient hWeil alpha beta d orbitExponent
        halpha hbeta hnondegenerate hd horbitPositive horbitChar hdvd horbitDvd
    rw [natCard_powerTraceRangeSolutions_swap
      (weightedSplitTorusTrace alpha beta)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p) orbitExponent d]
    simpa [ZMod.card] using hestimate
  simpa [splitPrimitiveTraceSolutions, primitiveTraceMoebiusMainTerm] using
    traceExactOrderSolutions_card_error_le_moebiusMain
      (weightedSplitTorusTrace alpha beta)
      (splitTorusTrace : (ZMod p)ˣ → ZMod p)
      orbitExponent
      (fun d => (p : ℝ) / ((d : ℝ) * (orbitExponent : ℝ)))
      ((coefficient : ℝ) * Real.sqrt (p : ℝ)) hRange

end SplitApplication
end
end BGS.Markoff
end
