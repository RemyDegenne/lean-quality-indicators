namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

namespace P2mKcUnitRootLattice

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]

variable {j : Zp2 p →+* k} (Φ : SpecialFormalODModule p j)

scoped instance free_piece (n : ℕ) : Module.Free (WittVector p k) (piece Φ n) :=
  Module.Free.of_basis (basis Φ n)

scoped instance finite_piece (n : ℕ) : Module.Finite (WittVector p k) (piece Φ n) :=
  Module.Finite.of_basis (basis Φ n)

noncomputable def LPi : Matrix (Fin 2) (Fin 2) k := linearPartHom Φ.F Φ.varpiEnd

end P2mKcUnitRootLattice
end P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
