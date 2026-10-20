namespace P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers

attribute [-instance] PrimaryTorsion.instSMul PrimaryTorsion.instModule

set_option autoImplicit false

open PDivisibleGroup Filter Topology

open scoped TensorProduct

namespace PDivINJK

variable (p : ℕ) [Fact p.Prime]

section Base

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem htf_K (x : OK p K) (hx : ((p : ℕ) : OK p K) * x = 0) : x = 0 := by
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ((((p : ℕ) : OK p K) * x : OK p K) : PadicAlgCl p) = 0 := by rw [hx]; rfl
  rw [Subalgebra.coe_mul] at h1
  have h2 : (((p : ℕ) : OK p K) : PadicAlgCl p) = (p : PadicAlgCl p) := rfl
  rw [h2] at h1
  exact Subtype.ext ((mul_eq_zero.mp h1).resolve_left hp0)

end Base
end PDivINJK
end P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
