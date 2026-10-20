namespace P2MW.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq

set_option autoImplicit false

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

set_option autoImplicit false

open scoped TensorProduct

open IsDedekindDomain NumberField

noncomputable section

namespace AdelicSlice

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm

end AdelicSlice
end
end P2MW.S_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq
