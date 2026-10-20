namespace P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits

set_option autoImplicit false

namespace P2mUnramifiedSemiLocalCharacter

open NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped TensorProduct

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

noncomputable def phi (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (w : v.Extension (𝓞 L)) :
    (w.1.adicCompletion L)ˣ →* ℂˣ where
  toFun t := ξL ⟨Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L w.1 t), Subgroup.mem_top _⟩
  map_one' := by simp only [map_one]; exact xi_mk_one L ξL
  map_mul' s t := by simp only [map_mul]; exact xi_mk_mul L ξL _ _

end P2mUnramifiedSemiLocalCharacter
end P2MW.S_TwistedUnipotentTerm_semiLocalCharacter_eq_finprod_zpow_neg_log_of_forall_mem_integralUnits
