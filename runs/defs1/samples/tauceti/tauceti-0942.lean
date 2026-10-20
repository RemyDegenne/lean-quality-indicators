public section

universe u v w

namespace FDRep

open CategoryTheory

section IsoToEquiv

variable {R : Type u} {G : Type v} [CommRing R] [Monoid G]

/-- **The equivalence of representations underlying an isomorphism in `FDRep R G`**: the linear
equivalence `FDRep.isoToLinearEquiv` intertwines the two actions, by `FDRep.Iso.conj_ρ`.  This is
the `FDRep` counterpart of `Representation.equivOfIso` for `Rep`, and the converse of
`LinearEquiv.toFDRepIso`. -/
noncomputable def isoToEquiv {V W : FDRep R G} (i : V ≅ W) : Representation.Equiv V.ρ W.ρ :=
  .mk (isoToLinearEquiv i) fun g => LinearMap.ext fun v => by
    simp [Iso.conj_ρ i g, LinearEquiv.conj_apply]

end IsoToEquiv
end FDRep
end
