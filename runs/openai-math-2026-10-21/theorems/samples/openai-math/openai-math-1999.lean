namespace OAI

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledYield

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity

open Filter

open scoped BigOperators Topology

theorem balanced_scheduledYield (K : ℕ) (hK : 2 ≤ K) (hgap : nativeB < nativeHigh) :
    scheduledYield K nativeLambda = (K : ℝ) * nativeCstar - nativeBeta :=
  FiniteSchedule.finite_schedule_yield K hK nativeLA nativeLB
    (nativeLC nativeLambda) nativeCstar (native_balanced hgap)

end MatrixMultiplication.AllFieldScheduledYield
end
end OAI
