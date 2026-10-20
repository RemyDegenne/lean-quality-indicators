@[expose] public section

namespace Submodule

universe uK uM

variable {K : Type uK} {M : Type uM}

variable [CommRing K] [AddCommGroup M] [Module K M]

variable (P : Submodule K M)

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

end Submodule
end
