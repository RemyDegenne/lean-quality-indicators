namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField

open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKcLevelTwistAction

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}

abbrev G (hΛ : IsOrder Λ) (m : ℕ) : Type := (Qring hΛ m)ˣ

end P2mKcLevelTwistAction
end P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_isLevelTwistAction
