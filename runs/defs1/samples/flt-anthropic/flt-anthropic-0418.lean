namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Topology

namespace HurTc

section

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def unitSphere : Subgroup (v.adicCompletion K)ˣ where
  carrier := {t | Valued.v (t : v.adicCompletion K) = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

end
end HurTc
end P2MW.S_IsDedekindDomain_HeightOneSpectrum_norm_apply_units_eq_one_of_valuation_eq_one_and_exists_isOpen_subgroup_apply_eq_one
