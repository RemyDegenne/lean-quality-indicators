namespace P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

open Polynomial

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

namespace WeierstrassCurve

p2m_open

variable {R : Type*} [CommRing R]

variable {S : Type*} [CommRing S]

namespace Universal

open WeierstrassCurve.S1Tail

theorem Ψ₂Sq_𝓦p_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (𝓦p p).Ψ₂Sq ≠ 0 := by
  intro h
  have := congrArg (fun q => Polynomial.coeff q 3) h
  simp [WeierstrassCurve.Ψ₂Sq, coeff_X, coeff_C, coeff_X_pow] at this
  exact four_ne_zero_Rp p hp2 this

end Universal
end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand
