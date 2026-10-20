public section

namespace TauCeti

universe u v w

section NatIndexed

variable (p n : ℕ) (rels : Set (freeProP p (Fin n)))

/-- The generators of a pro-`p` group presented on `Fin n`, indexed by `ℕ` with value `1` out of
range: the images of `TauCeti.freeProPGen`. -/
noncomputable def presentedProPGen (i : ℕ) : presentedProP p (Fin n) rels :=
  presentedProP.mk p rels (freeProPGen p n i)

end NatIndexed
end TauCeti
end
