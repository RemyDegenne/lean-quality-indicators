namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

variable (W : WeierstrassCurve R)

noncomputable def deuringA₁ (x y : R) : R := W.a₁ + 2 * W.tangentSlope x y

end WeierstrassCurve
