namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers

set_option autoImplicit false

open PDivisibleGroup Filter Topology

open scoped TensorProduct

namespace PDivDAlphaK

variable (p : ℕ) [Fact p.Prime]

section Generic

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]

noncomputable abbrev OR (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)] : Subalgebra R (PadicAlgCl p) :=
  integralClosure R (PadicAlgCl p)

end Generic
end PDivDAlphaK
end P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tateModule_padicComplex_smul_eq_and_norm_sub_le_of_ringOfIntegers
