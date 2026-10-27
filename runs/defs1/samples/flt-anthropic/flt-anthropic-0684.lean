namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace B14Lec

noncomputable section

namespace Setup

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {ℓ N : ℕ} [hℓ : Fact ℓ.Prime] [NeZero N]
  {M : Type} [AddCommGroup M] (X : Setup Λ ℓ N M)

scoped instance finite_S₀ : Finite X.S₀ :=
  Nat.finite_of_card_ne_zero (by rw [X.natCard_S₀]; exact pow_ne_zero _ (Nat.mul_ne_zero (NeZero.ne N) ℓ_ne))

scoped instance finite_C : Finite X.C :=
  Nat.finite_of_card_ne_zero (by rw [X.cardC]; exact pow_ne_zero _ (NeZero.ne N))

scoped instance finite_T : Finite X.T :=
  Nat.finite_of_card_ne_zero (by rw [X.natCard_T]; exact pow_ne_zero _ ℓ_ne)

def CS₀ : AddSubgroup X.S₀ := X.C.addSubgroupOf X.S₀

end Setup
end
end B14Lec
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_natCard_levelLift_eq_of_dvd
