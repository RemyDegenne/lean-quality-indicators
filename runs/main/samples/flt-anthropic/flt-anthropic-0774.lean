namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

open scoped Topology

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

open scoped Topology

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

open LanglandsTunnell.CubicInduction

open scoped Topology

set_option autoImplicit false

noncomputable section

p2m_open

set_option autoImplicit false

noncomputable section

p2m_open

open scoped ComplexConjugate

set_option autoImplicit false

noncomputable section

p2m_open

open scoped ComplexConjugate

namespace AbsIso

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

variable {T : V →ₗ[ℂ] V} {B : V → V → ℂ}

theorem Setup.apply_proj (h : Setup T B) (μ : ℂ) (v : V) : T (h.proj μ v) = μ • h.proj μ v :=
  EigenProj.apply_proj T _ μ v

end AbsIso
end
end
end
end
end P2MW.S_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable
