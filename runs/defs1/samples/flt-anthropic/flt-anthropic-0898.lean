namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

noncomputable section

namespace R3wSol

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

section Main

variable {q : ℕ} [hq : Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

def CommQ (u : Series k) : Prop :=
  (∀ i, constantCoeff (u i) = 0) ∧ ∀ i, subst u (X₀.F.nthSeries q i) = subst (X₀.F.nthSeries q) (u i)

end Main
end R3wSol
end
end P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_primitives_mod_nthSeries_typed_lines_of_finrank_eq_two
