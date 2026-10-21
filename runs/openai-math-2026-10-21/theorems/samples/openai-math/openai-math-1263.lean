namespace OAI

noncomputable section

namespace ComplexCancellation.LND

open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

@[simp] lemma orbit_coeff_zero (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 0 = r := by simp

end ComplexCancellation.LND
end
end OAI
