@[expose] public section

open Function

noncomputable section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)

/-- An equivalence of root pairings is a morphism where the maps of weight and coweight spaces are
bijective.

See also `RootPairing.Equiv.toEndUnit`. -/
@[ext]
protected structure Equiv extends Hom P Q where
  bijective_weightMap : Bijective weightMap
  bijective_coweightMap : Bijective coweightMap

end RootPairing
end
end
