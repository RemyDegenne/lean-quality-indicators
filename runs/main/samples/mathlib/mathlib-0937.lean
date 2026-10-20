@[expose] public section

noncomputable section

open Function Set Subalgebra MvPolynomial Algebra

variable {ι ι' : Type*} (R : Type*) {A A' : Type*} (x : ι → A)

variable [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

variable {R} {x}

open AlgebraicIndependent

@[simp]
lemma AlgebraicIndepOn.univ : AlgebraicIndepOn R x .univ ↔ AlgebraicIndependent R x :=
  algebraicIndependent_equiv (Equiv.Set.univ ι)

end
end
