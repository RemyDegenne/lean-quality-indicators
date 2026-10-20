public section

open Equiv MulAction

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace ConnectedFiberNumberedCover

variable (c : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

theorem connectedTriple_eq_connectedTriple_iff
    {c c' : ConnectedFiberNumberedCover (X := TopCat.of ThricePuncturedSphere) basePt n} :
    c.connectedTriple = c'.connectedTriple ↔ ConnectedFiberNumberedCoverIso c c' := by
  rw [connectedFiberNumberedCoverIso_iff_permCongrHom_comp_monodromyPerm_eq, Subtype.ext_iff,
    coe_connectedTriple, coe_connectedTriple, IsCoveringMap.monodromyTriple_def,
    IsCoveringMap.monodromyTriple_def, permutationTriple_injective.eq_iff]

end ConnectedFiberNumberedCover
end TauCeti
end
