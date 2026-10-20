public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

open scoped TensorProduct

universe u v v'

namespace QuadraticForm

variable {K : Type u} [Field K]

variable {V : Type v} [AddCommGroup V] [Module K V]

section Diagonal

variable {ι : Type*} [Fintype ι]

/-- A diagonal form localized at a finite place is canonically isometric to the diagonal form
whose coefficients are mapped into the completion. -/
def atFinitePlaceWeightedSumSquares [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : ι → K) :
    (atFinitePlace (QuadraticMap.weightedSumSquares K a) v).IsometryEquiv
      (QuadraticMap.weightedSumSquares (v.adicCompletion K) fun i =>
        algebraMap K (v.adicCompletion K) (a i)) := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let e := baseChangeWeightedSumSquares (A := v.adicCompletion K) a
  refine { toLinearEquiv := e, map_app' := ?_ }
  intro x
  simpa only [atFinitePlace] using e.map_app' x

end Diagonal
end QuadraticForm
end
end
