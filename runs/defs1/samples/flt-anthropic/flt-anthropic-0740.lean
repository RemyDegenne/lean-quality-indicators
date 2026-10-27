namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

namespace P2mKcCritFibre

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p]

variable {j : Zp2 p →+* k} (Φ : SpecialFormalODModule p j)

scoped instance free_piece (n : ℕ) : Module.Free (WittVector p k) (piece Φ n) :=
  Module.Free.of_basis (basis Φ n)

scoped instance finite_piece (n : ℕ) : Module.Finite (WittVector p k) (piece Φ n) :=
  Module.Finite.of_basis (basis Φ n)

noncomputable def piRes (n : ℕ) : piece Φ n →ₗ[WittVector p k] piece Φ (n + 1) where
  toFun f := ⟨endAct Φ.varpiEnd (f : CartierModule p Φ.F), pi_mem Φ n f.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' w f := Subtype.ext (pi_smul Φ w f)

end P2mKcCritFibre
end P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
