public section

namespace TauCeti

universe u

open Matrix

section CommRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (n : ℕ)

/-- **The tensor product of `det ^ λₙ` with the Weyl module of the polynomial part of `λ` is the
rational Weyl module**, the form in which the determinant twist is usually written.  The
equivalence is `TensorProduct.lid`: the tensor product with the line is the twist with the line
absorbed, which is `Representation.tprodEquivCharTwist` at the character `det ^ λₙ`. -/
noncomputable def tprodEquivRationalWeylRep (l : DominantWeight n) :
    ((detPowerRep k n l.detShift).tprod (weylRepOfShape k n l.detShiftShape)).Equiv
      (rationalWeylRep k n l) :=
  .mk (_root_.TensorProduct.lid k _) fun g => LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, detPowerRep_def, rationalWeylRep_apply]
    exact Representation.lid_ofLinearCharacter_tprod_apply _ _ g x

end CommRing
end TauCeti
end
