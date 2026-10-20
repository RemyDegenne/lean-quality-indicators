@[expose] public section

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

namespace Subspace

variable {K V}

theorem span_iUnion {ι} (s : ι → Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  (@gi K V _ _ _).gc.l_iSup

end Subspace
end Projectivization
end
