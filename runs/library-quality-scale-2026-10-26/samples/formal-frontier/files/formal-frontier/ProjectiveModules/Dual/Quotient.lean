/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Module.QuotientHom
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Quotient duality and the kernel of restriction

For a module over a commutative ring, the kernel of restriction of linear forms to a
submodule is its dual annihilator. Under this identification,
`Submodule.quotientHomEquivKer` agrees with Mathlib's
`Submodule.dualQuotEquivDualAnnihilator` as a linear equivalence, not just as a map on
representatives. Its forward map is the dual of the quotient map, and its inverse is
`Submodule.dualCopairing`.

The comparison allows direct reuse of
`Submodule.dualQuotEquivDualAnnihilator_apply` and
`Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk` after rewriting the equivalence.
The kernel identification is the equality
`Submodule.dualRestrict_ker_eq_dualAnnihilator`, rewritten using
`Submodule.dualRestrict_def` and `LinearMap.dualMap_eq_lcomp`. The range calculation
then uses `Submodule.range_dualMap_mkQ_eq` directly. No second quotient-duality
construction or copies of these characteristic lemmas are needed.

## References

This file uses Mathlib's quotient duality and annihilator formalization in
`Mathlib.LinearAlgebra.Dual.Defs` and `Mathlib.LinearAlgebra.Dual.Lemmas`, by Johan Commelin,
Fabian Glöckle, and Kyle Miller.
-/

@[expose] public section

namespace Submodule

universe uK uM

variable {K : Type uK} {M : Type uM}
variable [CommRing K] [AddCommGroup M] [Module K M]
variable (P : Submodule K M)

/-- The underlying forward map of the quotient-Hom equivalence is the dual of the quotient map
when both the coefficient module and its scalar ring are the base commutative ring. -/
theorem subtype_comp_quotientHomEquivKer_eq_dualMap :
    (LinearMap.ker (LinearMap.lcomp K K P.subtype)).subtype.comp
      (P.quotientHomEquivKer (S := K) (C := K)).toLinearMap = P.mkQ.dualMap := by
  ext φ x
  exact (P.quotientHomEquivKer_apply (S := K) (C := K) φ x).trans
    (LinearMap.dualMap_apply P.mkQ φ x).symm

/-- Over a commutative ring with coefficients in that ring, the quotient-Hom equivalence,
transported from the kernel of restriction to the dual annihilator, is Mathlib's quotient-dual
linear equivalence. -/
theorem quotientHomEquivKer_eq_dualQuotEquivDualAnnihilator :
    (P.quotientHomEquivKer (S := K) (C := K)).trans
      (LinearEquiv.ofEq (LinearMap.ker (LinearMap.lcomp K K P.subtype))
        P.dualAnnihilator (by
          rw [← LinearMap.dualMap_eq_lcomp, ← dualRestrict_def]
          exact P.dualRestrict_ker_eq_dualAnnihilator)) =
      P.dualQuotEquivDualAnnihilator := by
  -- Compare the ambient linear maps, rather than function coercions on the annihilator.
  have hforward :
      P.dualAnnihilator.subtype.comp P.dualQuotEquivDualAnnihilator.toLinearMap =
        P.mkQ.dualMap := by
    rw [dualQuotEquivDualAnnihilator, LinearEquiv.toLinearMap_ofLinearMap,
      LinearMap.subtype_comp_codRestrict]
  apply LinearEquiv.ext
  intro φ
  apply Subtype.ext
  simpa only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearEquiv.coe_toLinearMap] using
    LinearMap.congr_fun
      (P.subtype_comp_quotientHomEquivKer_eq_dualMap.trans hforward.symm) φ

/-- After identifying the restriction kernel with the dual annihilator, the inverse of the
quotient-Hom equivalence is the dual copairing. This is an equality of linear maps. -/
theorem quotientHomEquivKer_symm_eq_dualCopairing :
    (P.quotientHomEquivKer (S := K) (C := K)).symm.toLinearMap.comp
      (LinearEquiv.ofEq (LinearMap.ker (LinearMap.lcomp K K P.subtype))
        P.dualAnnihilator (by
          rw [← LinearMap.dualMap_eq_lcomp, ← dualRestrict_def]
          exact P.dualRestrict_ker_eq_dualAnnihilator)).symm.toLinearMap =
      P.dualCopairing := by
  have h := congrArg (fun e : Module.Dual K (M ⧸ P) ≃ₗ[K] P.dualAnnihilator =>
    e.symm.toLinearMap) P.quotientHomEquivKer_eq_dualQuotEquivDualAnnihilator
  simpa only [LinearEquiv.trans_symm, LinearEquiv.coe_trans] using
    h.trans P.dualCopairing_eq.symm

end Submodule
