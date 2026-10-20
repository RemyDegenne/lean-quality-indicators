namespace P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace P2MKcCB

variable {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]

variable (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)

theorem coe_e_Sg (v : ZMod n × ZMod n) : ((e (Sg e σ v) : Submodule.torsionBy ℤ A n) : A) = σ (e v : A) := by
  simp [Sg]

end P2MKcCB
end P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
