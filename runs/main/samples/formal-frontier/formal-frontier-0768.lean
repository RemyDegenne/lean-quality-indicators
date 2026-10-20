public section

set_option warningAsError true

open Set Function Topology TopologicalSpace

open CategoryTheory Limits

open scoped TensorProduct

namespace PrimeSpectrum

universe u

open AlgebraicGeometry

variable (k A B : Type u) [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B]

lemma connectedSpace_tensorProduct_left_iff_of_isPurelyInseparable
    (K R : Type u) [Field K] [Algebra k K] [IsPurelyInseparable k K]
    [CommRing R] [Algebra k R] :
    ConnectedSpace (PrimeSpectrum (K ⊗[k] R)) ↔ ConnectedSpace (PrimeSpectrum R) := by
  let e := Algebra.TensorProduct.comm k R K
  let hcomm := PrimeSpectrum.isHomeomorph_comap_of_bijective e.bijective
  let hpure := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable k K R
  exact hcomm.homeomorph.connectedSpace_iff.trans hpure.homeomorph.connectedSpace_iff

end PrimeSpectrum
end
