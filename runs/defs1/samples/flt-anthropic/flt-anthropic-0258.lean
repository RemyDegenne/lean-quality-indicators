namespace P2MW.S_AutomorphicForm_localChar_eq_one_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel_of_valued_sub_one_le

attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel

open IsDedekindDomain AutomorphicForm AdelicDock LocalGL2

open scoped NNReal

namespace PSUnramN

variable {K : Type} [Field K] [NumberField K]

section Torus

variable (v : HeightOneSpectrum (𝓞 K))

local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers K v

local notation "Kv" => HeightOneSpectrum.adicCompletion K v

def unitOf (t : (Kv)ˣ) (ht : (t : Kv) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (Kv)ˣ) : Kv) ∈ v.adicCompletionIntegers K) : (𝓞v)ˣ where
  val := ⟨t, ht⟩
  inv := ⟨((t⁻¹ : (Kv)ˣ) : Kv), hti⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

end Torus
end PSUnramN
end
end P2MW.S_AutomorphicForm_localChar_eq_one_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel_of_valued_sub_one_le
