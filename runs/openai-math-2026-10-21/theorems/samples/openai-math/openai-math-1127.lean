namespace OAI

noncomputable section

namespace StableCoordinate.FrameLift

open MvPolynomial

variable {k S T : Type*} [CommRing k] [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

theorem Frame.ideal_le_ker_polynomialMap (F : Frame S) (u : S) :
    Obstruction.idealC k ≤ RingHom.ker (F.polynomialMap (k := k) u).toRingHom := by
  rw [Obstruction.idealC, Ideal.span_singleton_le_iff_mem]
  exact F.polynomialMap_relation u

end StableCoordinate.FrameLift
end
end OAI
