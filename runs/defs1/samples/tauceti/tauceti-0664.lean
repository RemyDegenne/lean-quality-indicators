public section

namespace TauCeti

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The duality theorem** (Stichtenoth, Theorem 1.5.14): for `W` the divisor of a nonzero Weil
differential `ω`, multiplication by `ω` is a `k`-linear isomorphism `L(W - D) ≃ Ω_F(D)`. -/
noncomputable def riemannRochSpaceEquivWeilDifferentialFiltration (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)} (hω : ω ≠ 0)
    {W : Divisor k F}
    (hW : IsGreatest {D : Divisor k F | ω ∈ weilDifferentialFiltration D} W) (D : Divisor k F) :
    ↥(riemannRochSpace (W - D)) ≃ₗ[k] ↥(weilDifferentialFiltration D) :=
  (Submodule.equivMapOfInjective _ (repartitionDualMulRight_injective hF hω)
    (riemannRochSpace (W - D))).trans
      (LinearEquiv.ofEq _ _ (map_riemannRochSpace_repartitionDualMulRight hF hex hω hW D))

end TauCeti
end
