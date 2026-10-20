@[expose] public section

local notation "l(" x "," y ")" => y →ₗ[x] y

variable {R H₁ H₂ : Type _} [CommSemiring R]
  -- [semiring H₁] [semiring H₂]
  -- [algebra R H₁] [algebra R H₂]
  [NonUnitalNonAssocSemiring H₁]
  [Module R H₁] [SMulCommClass R H₁ H₁] [IsScalarTower R H₁ H₁] [NonUnitalNonAssocSemiring H₂]
  [Module R H₂] [SMulCommClass R H₂ H₂] [IsScalarTower R H₂ H₂]

open scoped TensorProduct

local notation x " ⊗ₘ " y => TensorProduct.map x y

open scoped BigOperators

theorem lmul_eq_zero_iff {H₁ : Type _} [Semiring H₁] [Algebra R H₁] (x : H₁) :
    (lmul x : l(R,H₁)) = 0 ↔ x = 0 :=
  LinearMap.mulLeft_eq_zero_iff _ _ _

end
