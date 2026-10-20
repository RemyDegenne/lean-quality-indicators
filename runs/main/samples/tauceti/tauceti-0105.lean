public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n) (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

@[simp]
theorem frobenius_zero : frobenius n hn p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, GeneralLinear.IntegralPointsPresentation.map_id]

end
end TauCeti.TypeDSpinCarrier
end
