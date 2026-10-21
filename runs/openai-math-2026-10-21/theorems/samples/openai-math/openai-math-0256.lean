namespace OAI

noncomputable section

namespace Problem355.RowLattice

theorem integerPlane_equalCoordinate_index
    (B k b e q : ℕ) [Fact q.Prime] (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hBq : IsUnit (B : ZMod q))
    (x z : Fin 3 → ℤ) (hz : x ⬝ᵥ z = 1) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q,
      reduction q x = a • PlaneFunctional.coordinateDifference i j) :
    (PlaneFunctional.equalCoordinateSubgroup q (integerPlane (B ^ k) C x) i j).index = q := by
  exact integerPlane_extra_equation_index B k b e q hbe C P Q hC hBq x z hz
    (PlaneFunctional.coordinateDifference i j)
    (PlaneFunctional.not_exists_smul_swap _ _
      (PlaneFunctional.coordinateDifference_ne_zero hij) hspan)

end Problem355.RowLattice
end
end OAI
