public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CompletedGroupAlgebra

/-- The underlying ring of the inverse limit of `R[G/U]` over all open normal
subgroups `U` of `G`.

The topology is asserted separately in
`IwasawaModules.CompletedGroupAlgebra.Topology`. -/
abbrev _root_.CompletedGroupAlgebra (R : Type u) [CommRing R] (G : ProfiniteGrp.{v}) :=
  limit (finiteQuotientSystem R G)

end CompletedGroupAlgebra
end
end
