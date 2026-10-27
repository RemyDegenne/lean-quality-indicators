public section

noncomputable section

open Module

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]

variable [Finite G]

namespace AuslanderReitenTranspose

variable {P₁ P₀ M : Type*} [AddCommGroup P₁] [Module (MonoidAlgebra ℤ_[p] G) P₁] [Module ℤ_[p] P₁]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P₁]
  [AddCommGroup P₀] [Module (MonoidAlgebra ℤ_[p] G) P₀] [Module ℤ_[p] P₀]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P₀] [Module.Projective ℤ_[p] P₀]
  [AddCommGroup M] [Module (MonoidAlgebra ℤ_[p] G) M] [Module ℤ_[p] M]
  [IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) M] [Module.Finite ℤ_[p] M]
  {f : P₁ →ₗ[MonoidAlgebra ℤ_[p] G] P₀} {π : P₀ →ₗ[MonoidAlgebra ℤ_[p] G] M}
  (hf : Function.Exact f π) (hfi : Function.Injective f) (hπ : Function.Surjective π)

/-- **The transpose of a `ℤ_p[G]`-module of projective dimension one is the Pontryagin dual of
its `p`-power torsion.** For a finite group `G` and an exact sequence `0 → P₁ → P₀ → M → 0` of
`ℤ_p[G]`-modules with `P₀` projective over `ℤ_p` and `M` finitely generated over `ℤ_p`, the
transpose `Tr f` (which is `E¹(M)` when `P₀` and `P₁` are projective over `ℤ_p[G]`) is isomorphic
to `Hom_{ℤ_p}(M[p^∞], ℚ_p / ℤ_p)`, compatibly with the action of `ℤ_p[G]ᵐᵒᵖ` on the transpose and
the contragredient action on characters. -/
def torsionDualLinearEquiv :
    AuslanderReitenTranspose f ≃ₗ[(MonoidAlgebra ℤ_[p] G)ᵐᵒᵖ]
      (pPowerTorsion p (MonoidAlgebra ℤ_[p] G) M →ₗ[ℤ_[p]]
        ℚ_[p] ⧸ (1 : Submodule ℤ_[p] ℚ_[p])) where
  __ := torsionDualAddEquiv hf hfi hπ
  map_smul' a x := LinearMap.ext fun t ↦ by
    induction x using induction_on with | h φ => ?_
    rw [AddEquiv.toFun_eq_coe, ← map_smul, torsionDualAddEquiv_mk,
      torsionDualAddEquiv_mk, RingHom.id_apply, ← MulOpposite.op_unop a]
    erw [DomMulAct.mk_smul_linearMap_apply (MulOpposite.unop a)]
    rw [map_smul, ← torsionDualMap_comp_toLinearMap_apply]
    -- The contragredient action of `op a` on a base-ring functional is precomposition with `a`.
    refine congrArg (torsionDualMap p hf hfi hπ · t) (LinearMap.ext fun m ↦ ?_)
    erw [DomMulAct.mk_smul_linearMap_apply (MulOpposite.unop a)]

end AuslanderReitenTranspose
end TauCeti
end
end
