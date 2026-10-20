public section

namespace TauCeti

open DoubledQuiver SimpleGraph

universe u w

namespace SkewZigzagParameter

variable {k : Type w} {V : Type u} {G : SimpleGraph V}

variable [CommMonoid k]

variable (k G) in
/-- The **cohomology class** of a skew-zigzag parameter in the first cohomology `H¹(G, kˣ)` of
the graph: the class of the `1`-cochain `h ↦ τ h / τ h.symm` for any edge coordinates `τ` with
`ratio(h, h') = τ h / τ h'` (see `cohomologyClass_eq_mk_of_ratio_eq_div`). -/
noncomputable def cohomologyClass : SkewZigzagParameter k G →* G.FirstCohomology kˣ :=
  (FirstCohomology.mk G kˣ).comp transitionCochain

end SkewZigzagParameter
end TauCeti
end
