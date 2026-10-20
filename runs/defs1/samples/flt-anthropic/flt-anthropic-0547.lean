namespace P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers

attribute [-instance] PrimaryTorsion.instSMul PrimaryTorsion.instModule

set_option autoImplicit false

open PDivisibleGroup Filter Topology

open scoped TensorProduct

namespace PDivINJK

variable (p : ℕ) [Fact p.Prime]

section Generic

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

noncomputable def ι (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : OR p R →+* ℂ_[p] :=
  (algebraMap (PadicAlgCl p) ℂ_[p]).comp (OR p R).val.toRingHom

end Generic
end PDivINJK
end P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers
