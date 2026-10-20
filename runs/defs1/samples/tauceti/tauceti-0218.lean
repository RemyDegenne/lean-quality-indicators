public section

namespace TauCeti

open Polynomial

attribute [local instance] Classical.propDecidable

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance] BinomialRing.toHasUniqueDiv

variable (K : Type*) [Ring K] [Algebra ℚ K]

/-- The binomial polynomials, ordered by degree, as a polynomial sequence. -/
noncomputable def binomialPolynomialSequence [Nontrivial K] : Polynomial.Sequence K where
  elems' := fun n => Ring.choose X n
  degree_eq' := degree_ringChoose_X K

end TauCeti
end
