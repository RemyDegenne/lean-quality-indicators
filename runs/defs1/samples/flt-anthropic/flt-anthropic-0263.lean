namespace P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half

set_option autoImplicit false

p2m_reactivate

noncomputable section

open NumberField IsDedekindDomain

open scoped Classical

namespace AutomorphicForm

namespace WeylIntegrable

p2m_open

p2m_reactivate

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

local notation "𝔸∞" => InfiniteAdeleRing F

local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

def selE (a : 𝔸∞) (b : 𝔸f) : 𝔸 := toAdele' F (fun w => if BigInf F a w then 1 else 0)
  (finOfIntegral F (fun v => if BigFin F b v then 1 else 0) fun v => by split_ifs <;> simp [one_mem, zero_mem])

end Adelic
end WeylIntegrable
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
