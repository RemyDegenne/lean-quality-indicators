namespace P2MW.S_CuspForm_traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero

set_option autoImplicit false

open ModularForm

theorem solution {M q : ℕ} [NeZero M]
    (A : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) (hqM : q ∣ M) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (h1 : CuspForm.traceLin A hq f = 0) (h2 : CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 f) = 0) :
    CuspForm.traceLin A hq (CuspForm.heckeULin 2 hqM f) = 0 ∧
      CuspForm.traceLin A hq (CuspForm.atkinLehnerLin A 2 (CuspForm.heckeULin 2 hqM f)) = 0 := by

  have hU : CuspForm.heckeULin 2 hqM f = -CuspForm.atkinLehnerLin A 2 f := by
    refine DFunLike.coe_injective ?_
    have h := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 A.R) 2 => (⇑g : UpperHalfPlane → ℂ)) h2
    have hww : alSlash A 2 (alSlash A 2 ⇑f) = ⇑f := by
      have := congrArg (fun g : CuspForm (CongruenceSubgroup.Gamma0 M) 2 => (⇑g : UpperHalfPlane → ℂ))
        (CuspForm.atkinLehnerLin_atkinLehnerLin A f)
      simpa only [CuspForm.coe_atkinLehnerLin_apply] using this
    simp only [CuspForm.coe_traceLin_apply, CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_zero, hww] at h
    show heckeU 2 q ⇑f = ⇑(-CuspForm.atkinLehnerLin A 2 f)
    rw [CuspForm.coe_neg, CuspForm.coe_atkinLehnerLin_apply]
    exact eq_neg_of_add_eq_zero_right h
  constructor
  · rw [hU, map_neg, h2, neg_zero]
  · rw [hU, map_neg, map_neg, CuspForm.atkinLehnerLin_atkinLehnerLin, h1, neg_zero]

end P2MW.S_CuspForm_traceLin_heckeULin_eq_zero_of_traceLin_eq_zero_of_traceLin_atkinLehnerLin_eq_zero
