namespace P2MW.S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain HeckeCharacter NumberField.AdelicLevel NumberField.TateGlobal

open scoped Topology

noncomputable section

namespace R4Adm

variable (K : Type) [Field K] [NumberField K]

variable {K}

omit [NumberField K] in
theorem boxModulus_ne_bot (I : Finset (HeightOneSpectrum (𝓞 K))) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    boxModulus I n ≠ ⊥ := by
  unfold boxModulus
  rw [Ne, ← Submodule.zero_eq_bot, Finset.prod_eq_zero_iff]
  rintro ⟨v, _, hv⟩
  exact v.ne_bot (by rw [← Submodule.zero_eq_bot]; exact eq_zero_of_pow_eq_zero hv)

end R4Adm
end
end P2MW.S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
