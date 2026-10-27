public section

namespace TauCeti

open scoped BigOperators

open YoungTableau

/-- The **Specht module** `S^μ` of a partition `μ` of `n`, bundled as a finite-dimensional
representation of `Sₙ`: the span of the polytabloids of the tableaux of the Young diagram
`YoungDiagram.ofPartition μ`, with the symmetric group on the `(YoungDiagram.ofPartition μ).card`
entries of such a tableau identified with `Sₙ` along `YoungDiagram.card_ofPartition`.

The tabloid combinatorics is indexed by a diagram, since a tableau is a filling of one, while the
classification the Specht modules feed is indexed by partitions; this is the partition-indexed
name.  Its representation unfolds to `spechtSubrepresentation (YoungDiagram.ofPartition μ)` by
`FDRep.of_ρ'`, and `spechtSubrepresentation_toSubmodule` identifies the underlying module with the
span of the polytabloids. -/
noncomputable abbrev spechtModule {n : ℕ} (μ : n.Partition) :
    FDRep ℚ (Equiv.Perm (Fin n)) :=
  FDRep.of ((spechtSubrepresentation (YoungDiagram.ofPartition μ)).toRepresentation.comp
    (finCongr (YoungDiagram.card_ofPartition μ).symm).permCongrHom.toMonoidHom)

end TauCeti
end
