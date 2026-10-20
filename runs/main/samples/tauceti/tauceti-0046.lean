public section

namespace TauCeti

open scoped Topology

open unitInterval

variable {N : Type*}

theorem Cube.mk_mem_prodBoundary {s : I} {t : I^N} (h : s = 1 ∨ t ∈ Cube.boundary N) :
    ((s, t) : I × I^N) ∈ Cube.prodBoundary N :=
  h.elim (fun hs => .inl (.inr hs)) .inr

end TauCeti
end
