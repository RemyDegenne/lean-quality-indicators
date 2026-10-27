namespace P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange

set_option autoImplicit false

open scoped TensorProduct

universe u v

noncomputable section

namespace SupModelProof

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Main

set_option linter.unusedSectionVars false

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {H₀ : Type v} [CommRing H₀] [HopfAlgebra R H₀] [Module.Finite R H₀] [Module.Flat R H₀]
  [Coalgebra.IsCocomm R H₀]
  {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
  [Coalgebra.IsCocomm R H]
  (lam : (K ⊗[R] H₀) ≃ₐ[K] (K ⊗[R] H))

local notation "G" => H₀ ⊗[R] H

local notation "E" => K ⊗[R] H

local notation "Q" => QS (kerI K lam)

local notation "πQ" => QS.mk R (kerI K lam)

scoped instance : Module.Finite R Q := QS.moduleFinite R (kerI K lam)

scoped instance : Module.Free R Q :=
  free_of_injective K (muQ K lam).toLinearMap (muQ_injective K lam)

def thetaR : Q →ₐ[R] E ⊗[K] E :=
  ((Algebra.TensorProduct.includeRight (R := K) (A := E) (B := E)).restrictScalars R).comp
    (muQ K lam)

end Main
end SupModelProof
end
end P2MW.S_HopfAlgebra_exists_finiteFlat_model_bialgHom_surjective_baseChange_of_algEquiv_baseChange
