namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq

set_option autoImplicit false

open scoped TensorProduct

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace X2Body

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

variable {B : Type} [CommRing B] [Algebra 𝒪 B]

section Chart

variable [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] {π : 𝒪}

variable {M' M : FullLattice 𝒪 K} (d : DeligneDatum (K := K) π B)

scoped instance instInvertibleT0 (M' : FullLattice 𝒪 K) : Module.Invertible B (T0 d M') := d.invertible M'

theorem mem_S0_or_mem_S1 (hπ : Irreducible π) (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : PrimeSpectrum B) :
    x ∈ S0 d (M := M) hle ∨ x ∈ S1 d hπ hπM := by
  have hπmem : algebraMap 𝒪 B π ∈ x.asIdeal := by
    obtain ⟨n, hn⟩ := hB
    exact x.isPrime.mem_of_pow_mem n (hn ▸ x.asIdeal.zero_mem)
  exact Module.Invertible.range_le_smul_top_or_of_comp_eq_smul (Pi0 d hle) (Pi1 d hπ hπM) _
    (Pi1_comp_Pi0 d hπ hle hπM) x hπmem

end Chart
end X2Body
end P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_isQuadrupleOf_and_pi_eq_smul_chartERing_of_line_eq
