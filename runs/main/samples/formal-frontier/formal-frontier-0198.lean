@[expose] public section

noncomputable section

universe u

namespace Subgroup.RightTransversal

variable {G : Type u} [Group G]

@[simp]
lemma towerDecompositionEquiv_symm_apply (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal)
    (j : J) (p : ↥(U : Set K) × ↥(T : Set G)) :
    (towerDecompositionEquiv K J U T).symm (j, p) =
      ((((j : K) : G) * ((p.1 : K) : G)) * (p.2 : G)) := by
  change T.2.equiv.symm (U.2.equiv.symm (j, p.1), p.2) = _
  rw [T.2.equiv_symm_apply, U.2.equiv_symm_apply]
  rfl

end Subgroup.RightTransversal
end
end
