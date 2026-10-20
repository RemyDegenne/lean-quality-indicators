set_option warningAsError true

public section

noncomputable section

open AlgebraicGeometry

namespace ProjectiveSpace

universe u v w

variable {k : Type u} {V : Type v} {I : Type w} [Field k]

variable [AddCommGroup V] [Module k V]

local instance instDecidableEqSymmetricAlgebraAffineClosedPoint : DecidableEq I :=
  Classical.decEq I

theorem mvPolynomialAffineCoordinatePoint_isClosed (a : I → k) :
    IsClosed ({mvPolynomialAffineCoordinatePoint a} :
      Set (PrimeSpectrum (MvPolynomial I k))) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 <| by
    rw [mvPolynomialAffineCoordinatePoint_asIdeal]
    exact RingHom.ker_isMaximal_of_surjective
      (MvPolynomial.aeval a).toRingHom
      (fun c ↦ ⟨MvPolynomial.C c, by simp⟩)

end ProjectiveSpace
end
end
