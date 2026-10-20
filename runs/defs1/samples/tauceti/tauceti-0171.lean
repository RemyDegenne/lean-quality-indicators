public section

namespace TauCeti

namespace TypeCLieIndex

variable (d : TypeCLieIndex)

noncomputable section

/-- **The prime-field Frobenius of the standard symplectic carrier attached to a validated type-`C`
index**, the `p`-power map for `p` the defining characteristic. The `q`-power Frobenius is its
`e`-th power, for `e` the field exponent the index records, by
`frobenius_eq_primeFrobenius_pow`. -/
def primeFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  SpStd.frobenius d.carrierRank d.1.characteristic 1 d.1.Closure

end
end TypeCLieIndex
end TauCeti
end
