public section

namespace ParallelPostulate

namespace Pairs

section Ring

variable {K : Type*} [CommRing K]

namespace Dim

/-- The points of a dimension. -/
@[expose] def points (L : Dim K) : Set (K × K) := Set.range L.pt

end Dim
end Ring
end Pairs
end ParallelPostulate
end
