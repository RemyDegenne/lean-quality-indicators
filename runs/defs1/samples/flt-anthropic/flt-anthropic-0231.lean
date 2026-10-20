namespace P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring

set_option autoImplicit false

open scoped Kronecker

namespace MatrixUnitsRebase

open Matrix

variable {K : Type} [Field K] (𝒪 : ValuationSubring K)

variable {n : Type} [Fintype n] [DecidableEq n]
  (ρ : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2 × n) (Fin 2 × n) K)
  (hρ : ∀ m : Matrix (Fin 2) (Fin 2) K, (∀ i j, m i j ∈ 𝒪) → ∀ i j, ρ m i j ∈ 𝒪)

noncomputable def f (a b : Fin 2) : (Fin 2 × n → 𝒪) →ₗ[𝒪] (Fin 2 × n → 𝒪) :=
  Matrix.toLin' (R 𝒪 ρ hρ (single a b 1))

end MatrixUnitsRebase
end P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring
