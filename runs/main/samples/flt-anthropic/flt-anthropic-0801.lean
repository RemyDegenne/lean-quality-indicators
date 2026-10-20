namespace P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open PDivisibleGroup Coalgebra WithConv

p2m_open_scoped

namespace PDivMTower

variable {R : Type} [CommRing R] {p h : ℕ}

section Adjunction

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

variable {L : Type} [CommRing L] [Algebra R L]

theorem dualMap_transition_toDualEquiv (v : ℕ) (x' : G'.level (v + 1)) :
    (G.transitionAlgHom v).toLinearMap.dualMap (D.toDualEquiv v (G'.transition v x')) =
      D.toDualEquiv (v + 1) (Hopf.nsmulAlgHom R (G'.level (v + 1)) p x') := by
  refine LinearMap.ext fun a => ?_
  rw [LinearMap.dualMap_apply, CartierDuality.toDualEquiv_apply, CartierDuality.toDualEquiv_apply]
  change D.equiv v (G'.transition v x') (G.transition v a) =
    ((D.equiv (v + 1) : G'.level (v + 1) →ₐc[R] CartierDual R (G.level (v + 1)))
      (Hopf.nsmulAlgHom R (G'.level (v + 1)) p x')) a
  rw [D.equiv_transition v x' a, ← Hopf.nsmulAlgHom_bialgHom_apply, nsmulAlgHom_cartierDual_apply]
  rfl

end Adjunction
end PDivMTower
end
end P2MW.S_PDivisibleGroup_CartierDuality_mem_of_forall_pair_eq_one_and_exists_tateModule_forall_pair_eq_one
