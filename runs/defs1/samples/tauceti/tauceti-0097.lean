public section

noncomputable section

open Finset QuadraticMap

namespace QuadraticForm

variable {M M' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup M'] [Module ℝ M']
  [FiniteDimensional ℝ M] [FiniteDimensional ℝ M']

/-- The normal form of signature `(p, q)`: the orthogonal sum of `p` copies of `⟨1⟩` and `q`
copies of `⟨-1⟩`. -/
def realSignatureForm (p q : ℕ) : _root_.QuadraticForm ℝ (Fin p ⊕ Fin q → ℝ) :=
  weightedSumSquares ℝ (Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1)

end QuadraticForm
end
end
