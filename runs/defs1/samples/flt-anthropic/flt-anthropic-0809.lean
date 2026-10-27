namespace P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain Topology

noncomputable section

p2m_reactivate

p2m_reactivate

namespace Ws31

namespace FinUnit

variable (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K))

def T (v : HeightOneSpectrum (𝓞 K)) [Fact (N ≠ ⊥)] (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : Triv K N v χ) :
    (O K v ⧸ U' K N v) → rootsOfUnity (idx K N v) ℂ := fun q =>
  ⟨ψ K N v χ hχ q, by
    rw [mem_rootsOfUnity, ← map_pow, idx, pow_card_eq_one', map_one]⟩

end FinUnit
end Ws31
end
end P2MW.S_NumberField_exists_finite_forall_localFamily_eq_on_units_of_trivial_on_congruenceUnits
