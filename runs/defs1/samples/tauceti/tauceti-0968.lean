public section

namespace TauCeti

open LieAlgebra LieModule Module

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable (K : Type*) [CommRing K] (n : ℕ)

namespace Sl2Std

variable {K n}

variable (K n)

variable {K n}

section BasisVector

variable {i : ℕ}

variable (K n i) in
/-- The `i`-th vector of the coordinate basis of `V(n)`, extended by zero for `i` past the end of
the weight string. Indexing by `ℕ` rather than by `Fin (n + 1)` lets finite sums use natural
indices without carrying bounds through every rewrite. -/
noncomputable def basisVector : Sl2Std K n := if h : i < n + 1 then basis K n ⟨i, h⟩ else 0

end BasisVector
end Sl2Std
end CommRing
end TauCeti
end
