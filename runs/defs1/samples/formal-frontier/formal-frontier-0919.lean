@[expose] public section

noncomputable section

universe u

namespace Subgroup.RightTransversal

variable {G : Type u} [Group G]

/-- Decompose an ambient group element successively along a subgroup tower. -/
def towerDecompositionEquiv (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    G ≃ J × (↥(U : Set K) × ↥(T : Set G)) :=
  T.2.equiv |>.trans <|
    (Equiv.prodCongr U.2.equiv (Equiv.refl _)).trans
      (Equiv.prodAssoc J ↥(U : Set K) ↥(T : Set G))

end Subgroup.RightTransversal
end
end
