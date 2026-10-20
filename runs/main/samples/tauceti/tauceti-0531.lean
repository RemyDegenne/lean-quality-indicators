public section

open WithConv

namespace TauCeti.SpStd

universe v

noncomputable section

variable (n p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]

@[simp]
theorem frobenius_zero : frobenius n p 0 A = MonoidHom.id _ := by
  rw [frobenius, iterateFrobenius_zero, GeneralLinear.IntegralPointsPresentation.map_id]

end
end TauCeti.SpStd
end
