public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

/-- Mathlib's boundary `TopCat.diskBoundary n` of the `n`-disk, the universe lift of the unit
sphere of `EuclideanSpace ℝ (Fin n)`, is homeomorphic to the unit sphere of the Euclidean space
`EuclideanSpace ℝ (ULift (Fin n))` of the same dimension in the lifted universe. -/
def diskBoundaryHomeomorph (n : ℕ) :
    TopCat.diskBoundary.{u} n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (ULift.{u} (Fin n))) 1 :=
  Homeomorph.ulift.trans <|
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.ulift.{u}.symm : Fin n ≃ ULift.{u} (Fin n)))
      |>.toHomeomorph.subtype fun x ↦ by simp

end TauCeti
end
end
