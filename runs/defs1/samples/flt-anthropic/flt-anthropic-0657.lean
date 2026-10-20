namespace P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Coalgebra

p2m_open_scoped

namespace PDivRootR

variable (p : ℕ) [Fact p.Prime]

section Root

variable (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] {h : ℕ} (G : PDivisibleGroup R p h) (X : G.CPoints S)

def gε (v : ℕ) : G.level v →ₐ[R] S ⧸ mS p S :=
  ((Ideal.Quotient.mkₐ R (mS p S)).comp (Algebra.ofId R S)).comp (Bialgebra.counitAlgHom R (G.level v))

end Root
end PDivRootR
end
end P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
