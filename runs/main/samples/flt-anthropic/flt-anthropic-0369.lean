namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq

set_option autoImplicit false

open Coalgebra Bialgebra WithConv PDivisibleGroup

p2m_open_scoped

p2m_reactivate

namespace PDivEXPR

open PDivEXPRConv

variable (p : ℕ)

p2m_reactivate

variable {R : Type} [CommRing R]

variable {h : ℕ} {G : PDivisibleGroup R p h}

variable (hT : Tower p G) (τ : G.tangentSpace R)

theorem lam_add (τ' : G.tangentSpace R) (w i : ℕ) (hiw : i ≤ w) :
    lam p hT (τ + τ') w i hiw = lam p hT τ w i hiw + lam p hT τ' w i hiw := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hT.surj w y
  rw [LinearMap.add_apply, lam_proj, lam_proj, lam_proj, LinearMap.add_apply, map_add]

end PDivEXPR
end P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
