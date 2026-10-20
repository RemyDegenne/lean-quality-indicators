public section

open Matrix Module

namespace TauCeti

universe u v w

noncomputable section

variable {K : Type u} {G : Type w} {V : Type v}

variable [Field K] [Group G] [AddCommGroup V] [Module K V]

theorem _root_.Representation.exists_basis_isUpperUnitriangular_of_le_normalizer_isUnipotent
    [FiniteDimensional K V]
    (rho : Representation K G V) (U W : Subgroup G)
    (hWU : W ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ⊔ W = ⊤)
    (hU : ∀ u : U, IsNilpotent (rho u - 1))
    (hW : ∀ w : W, IsNilpotent (rho w - 1)) :
    ∃ (n : ℕ) (b : Basis (Fin n) K V),
      ∀ g, (LinearMap.toMatrixAlgEquiv b (rho g)).IsUpperUnitriangular :=
  rho.exists_basis_isUpperUnitriangular_of_isUnipotent
    (rho.isNilpotent_sub_one_of_normal_isUnipotent U W hWU hUW hU hW)

end
end TauCeti
end
