@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option linter.mathlibStandardSet true

set_option linter.style.header false

set_option warningAsError true

noncomputable section

open Polynomial

namespace QuadraticAlgebra

universe u

variable {R : Type u} [Field R]

/-- Coordinates for the existing quotient by a monic quadratic of degree two.
The chosen witness has square the negative discriminant of the coefficient
form `p = definingPolynomial (-p.coeff 0) (-p.coeff 1)`. Irreducibility is not
needed once that witness is supplied. -/
noncomputable def adjoinRootEquivOfDiscrSqNeg [NeZero (2 : R)] (p : R[X]) (hp : p.Monic)
    (hdeg : p.natDegree = 2) (d : R) (hd : d ≠ 0)
    (hd_sq : d ^ 2 = -(discr (-p.coeff 0) (-p.coeff 1))) :
    AdjoinRoot p ≃ₐ[R] QuadraticAlgebra R (-1) 0 := by
  have hcoeff : p.coeff 2 = 1 := by
    simpa only [hdeg] using hp.coeff_natDegree
  have heq : p = definingPolynomial (-p.coeff 0) (-p.coeff 1) := by
    calc
      p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
        eq_quadratic_of_degree_le_two (degree_le_of_natDegree_le hdeg.le)
      _ = definingPolynomial (-p.coeff 0) (-p.coeff 1) := by
        rw [hcoeff]
        simp only [definingPolynomial, Polynomial.C_1, one_mul, map_neg]
        ring
  exact (AdjoinRoot.algEquivOfEq R p
      (definingPolynomial (-p.coeff 0) (-p.coeff 1))
      heq).trans
    ((equivAdjoinRoot (-p.coeff 0) (-p.coeff 1)).symm.trans
      (equivOfDiscrSqNeg (-p.coeff 0) (-p.coeff 1) d hd hd_sq))

end QuadraticAlgebra
end
end
