namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel

set_option autoImplicit false

noncomputable section

namespace SolRaisedLevelHeckeChar

open ModularForm

section RaisedLevel

open FreyPackage.ModMCarrier

variable {N q' : ℕ} [NeZero (N * q')]

theorem heckeTLin_raise {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : CuspForm.IsNormalizedEigenform f) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q') :
    CuspForm.heckeTLin 2 hℓ hℓM (raise f) = ModularFormClass.qCoeff f ℓ • raise f := by
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.mul_right q')
  apply DFunLike.coe_injective
  have hN := congrArg DFunLike.coe
    (CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul N f hf ℓ hℓ hℓN)
  rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul] at hN
  change ⇑(CuspForm.heckeTLin 2 hℓ hℓM (raise f)) = ⇑(ModularFormClass.qCoeff f ℓ • raise (q' := q') f)
  rw [CuspForm.coe_heckeTLin_apply, CuspForm.IsGLPos.coe_smul, coe_raise]
  exact hN

end RaisedLevel
end SolRaisedLevelHeckeChar
end
end P2MW.S_CuspForm_IsNormalizedEigenform_exists_heckeAlgebraChar_raisedLevel
