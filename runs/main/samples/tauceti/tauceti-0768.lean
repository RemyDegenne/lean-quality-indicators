public section

open Polynomial

namespace AddSubgroup

section CommRing

variable {R : Type*} [CommRing R] (V : AddSubgroup R) [Fintype V]

@[simp]
theorem natDegree_additivePolynomial [Nontrivial R] :
    V.additivePolynomial.natDegree = Fintype.card V := by
  rw [additivePolynomial, Lagrange.natDegree_nodal, Finset.card_univ]

end CommRing
end AddSubgroup
end
