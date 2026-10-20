namespace HeckeEis

open MvPolynomial ModularCurve

open scoped MatrixGroups

section BinaryForms

variable (K : Type*) [CommRing K]

abbrev BinaryForm (n : ℕ) : Submodule K (MvPolynomial (Fin 2) K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K n

end BinaryForms
end HeckeEis
