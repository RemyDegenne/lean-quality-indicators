namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

namespace P2mKcBC52Module

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p]

variable {j : Zp2 p →+* k}

section OneModule

variable (X : SpecialFormalODModule p j)

variable {X}

variable (D : LatticeData X)

theorem pi_sumE (w : Fin 2 → WittVector p k) :
    endAct X.varpiEnd (sumE D w) = verschiebung (sumE D (fun r => WittVector.frobenius (w r))) := by
  rw [sumE_def, sumE_def, map_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pi_smul, D.pi_eq r, smul_verschiebung]

end OneModule
end P2mKcBC52Module
end P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_addMonoidHom_cartierModule_injective_of_isAlgClosed
