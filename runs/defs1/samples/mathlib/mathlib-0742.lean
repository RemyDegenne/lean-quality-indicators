@[expose] public section

noncomputable section

open Finsupp hiding single

open Module

variable {R S M N O G : Type*}

namespace MonoidAlgebra

section SMul

section Module

variable [Semiring R] [Semiring S] [Module R S] {s t : Set M} {x : S[M]}

variable (R S s) in
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/
@[to_additive
/-- The `R`-submodule of all elements of `S[M]` supported on a subset `s` of `M`. -/]
def supported : Submodule R S[M] := (Finsupp.supported S R s).comap (coeffLinearEquiv R).toLinearMap

end Module
end SMul
end MonoidAlgebra
end
end
