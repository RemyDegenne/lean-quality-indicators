public section

open Equiv MulAction

namespace TauCeti

open ThricePuncturedSphere

variable {n : ℕ}

namespace ConnectedFiberNumberedCoverClass

/-- **Numbered covers of `ℂ ∖ {0, 1}` up to label-preserving isomorphism are classified by their
connected triples.** -/
noncomputable def tripleEquiv :
    ConnectedFiberNumberedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n ≃
      ConnectedTriple n :=
  Equiv.ofBijective triple triple_bijective

end ConnectedFiberNumberedCoverClass
end TauCeti
end
