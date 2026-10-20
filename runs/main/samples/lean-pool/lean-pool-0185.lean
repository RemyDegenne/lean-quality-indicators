@[expose] public section

namespace Stafford38.Characteristic.BaseRelativePoisson

open Stafford38.Characteristic

open Stafford38.Geometry.CoisotropicTranslation

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

theorem fibreLinePolynomial_eq_zero_of_isBaseRelativePoisson
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsBaseRelativePoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    fibreLinePolynomial y (differentialAt y f) g = 0 := by
  apply polynomial_eq_zero_of_eval_iterate_derivative_zero
  intro m
  rw [iterate_derivative_fibreLinePolynomial, eval_zero_fibreLinePolynomial]
  exact hzero _ (hamiltonIter_mem_of_isBaseRelativePoisson J hJ f hf g hg m)

end
end Stafford38.Characteristic.BaseRelativePoisson
end
