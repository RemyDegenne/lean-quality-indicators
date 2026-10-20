public section

namespace TauCeti

namespace RankTwoBLieIndex

open DynkinType

noncomputable section

variable (d : RankTwoBLieIndex)

/-- **The prime-field Frobenius endomorphism of the ambient group of an index on the `B₂`
diagram**, the `p`-power map for `p` the defining characteristic. It agrees with the `q`-power map
`TauCeti.RankTwoBLieIndex.frobenius` above exactly when the index has field order `p`, which
happens on an untwisted branch of prime field order and never on a Suzuki index, whose validity
forces `q = 2 ^ (2m+1)` with `1 ≤ m`. It is the map that the half-Frobenius of a Suzuki index
squares to. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius 1 d.1.characteristic 1 d.1.Closure

end
end RankTwoBLieIndex
end TauCeti
end
