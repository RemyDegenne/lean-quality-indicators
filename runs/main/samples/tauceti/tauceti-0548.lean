public section

open Finset TensorProduct

universe u v

noncomputable section

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

namespace TauCeti

variable {R : Type v} [CommRing R] [Algebra ℤ R]

attribute [local instance high] Algebra.toModule

theorem baseChangeExp_lie (D : LieDerivation ℚ L L) (M : LieSubalgebra ℤ L)
    (hM : ∀ n, ∀ x ∈ M, Associative.dividedPower n D.toLinearMap x ∈ M)
    (hD : IsNilpotent D.toLinearMap) (t : R) (x y : R ⊗[ℤ] M) :
    baseChangeExp D.toLinearMap M hM t ⁅x, y⁆ =
      ⁅baseChangeExp D.toLinearMap M hM t x,
        baseChangeExp D.toLinearMap M hM t y⁆ := by
  let _ : LieRing (R ⊗[ℤ] M) := LieAlgebra.ExtendScalars.instLieRing ℤ R M
  let _ : LieAlgebra R (R ⊗[ℤ] M) := LieAlgebra.ExtendScalars.instLieAlgebra ℤ R M
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y => exact baseChangeExp_tmul_lie D M hM hD t a b x y
      | add y z hy hz =>
          rw [lie_add, map_add, hy, hz]
          rw [map_add, lie_add]
  | add x z hx hz =>
      rw [add_lie, map_add, hx, hz]
      rw [map_add, add_lie]

end TauCeti
end
end
