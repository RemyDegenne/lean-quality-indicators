public section

open Finset

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- The **dimension** of an abstract simplicial complex, defined through its underlying
precomplex. -/
noncomputable def dimension (K : AbstractSimplicialComplex ι) : WithBot ℕ∞ :=
  PreAbstractSimplicialComplex.dimension K.toPreAbstractSimplicialComplex

end AbstractSimplicialComplex
end
