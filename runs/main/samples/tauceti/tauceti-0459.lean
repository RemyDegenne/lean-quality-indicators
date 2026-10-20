public section

namespace TauCeti.Isogeny

open _root_.Polynomial

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (W : WeierstrassCurve.Affine F)

theorem xCoord_tautologicalPoint_iterateRelativeFrobeniusIsogeny [W.IsElliptic] (n : ℕ) :
    Point.xCoord (CoordinatePullback.tautologicalPoint
      (iterateRelativeFrobeniusIsogeny p W n).pullback) =
      W.genericX ^ p ^ n := by
  rw [CoordinatePullback.xCoord_tautologicalPoint, iterateRelativeFrobeniusIsogeny_pullback,
    iterateRelativeFrobeniusPullback_apply, CoordinateRing.iterateRelativeFrobenius_of,
    algebraMap_of_expand_X]

end TauCeti.Isogeny
end
