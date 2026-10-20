public section

set_option warningAsError true

namespace MvPolynomial

universe u v w

variable {R : Type u} {S : Type v} {V : Type w}

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem eval_addMonoidAlgebraMap_of_linearMap (lambda : S →ₗ[R] R)
    (F : MvPolynomial V S) (y : V → R) :
    lambda (MvPolynomial.eval (algebraMap R S ∘ y) F) =
      MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom F) := by
  classical
  have monomial_case (monomialIndex : V →₀ ℕ) (coefficient : S) :
      lambda (MvPolynomial.eval (algebraMap R S ∘ y)
        (MvPolynomial.monomial monomialIndex coefficient)) =
      MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom
        (MvPolynomial.monomial monomialIndex coefficient)) := by
    change lambda (MvPolynomial.eval (algebraMap R S ∘ y)
      (MvPolynomial.monomial monomialIndex coefficient)) =
      MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom
        (AddMonoidAlgebra.single monomialIndex coefficient))
    rw [AddMonoidAlgebra.map_single]
    change lambda (MvPolynomial.eval (algebraMap R S ∘ y)
      (MvPolynomial.monomial monomialIndex coefficient)) =
      MvPolynomial.eval y (MvPolynomial.monomial monomialIndex (lambda coefficient))
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    have hprod : monomialIndex.prod (fun index exponent =>
        (algebraMap R S (y index)) ^ exponent) =
        algebraMap R S (monomialIndex.prod (fun index exponent =>
          y index ^ exponent)) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    simp only [Function.comp_apply]
    rw [hprod, mul_comm coefficient]
    rw [← Algebra.smul_def]
    rw [lambda.map_smul, smul_eq_mul, mul_comm]
  calc
    lambda (MvPolynomial.eval (algebraMap R S ∘ y) F) =
        ∑ monomialIndex ∈ F.support,
          lambda (MvPolynomial.eval (algebraMap R S ∘ y)
            (MvPolynomial.monomial monomialIndex (F.coeff monomialIndex))) := by
      conv_lhs => rw [F.as_sum]
      rw [MvPolynomial.eval_sum, map_sum]
    _ = ∑ monomialIndex ∈ F.support,
          MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom
            (MvPolynomial.monomial monomialIndex (F.coeff monomialIndex))) := by
      apply Finset.sum_congr rfl
      intro monomialIndex _
      exact monomial_case monomialIndex (F.coeff monomialIndex)
    _ = MvPolynomial.eval y (AddMonoidAlgebra.map lambda.toAddMonoidHom F) := by
      conv_rhs => rw [F.as_sum]
      rw [AddMonoidAlgebra.map_sum, MvPolynomial.eval_sum]

end MvPolynomial
end
