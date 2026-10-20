namespace P2MW.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace LevelNormal

variable {K : Type} [Field K] [NumberField K]

local notation "𝔸f" => FiniteAdeleRing (𝓞 K) K

local notation "Gf" => GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)

structure IsPrincipalMatrix (N : Ideal (𝓞 K)) (m : Matrix (Fin 2) (Fin 2) 𝔸f) : Prop where
  integral : ∀ i j, m i j ∈ integralFiniteAdeles (𝓞 K) K
  cong : ∀ i j, m i j - (1 : Matrix (Fin 2) (Fin 2) 𝔸f) i j ∈ idealBall (𝓞 K) K N

end LevelNormal
end P2MW.S_NumberField_AdelicLevel_conj_mem_principalLevel_inf_finiteAdelicGL2Subgroup_of_mem_adelicMaximalCompact
