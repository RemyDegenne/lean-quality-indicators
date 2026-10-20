set_option warningAsError true

open Module MvPolynomial

open scoped TensorProduct

namespace Algebra

variable {R B A ι : Type*} [CommRing R] [Ring B] [Algebra R B]
  [CommRing A] [Algebra R A] [Fintype ι]

public section

theorem norm_coordinates_baseChange [DecidableEq ι] [Module.Free R B] [Module.Finite R B]
    (b : Basis ι R B) (x : ι → A) :
    MvPolynomial.aeval x
        (MvPolynomial.C ((-1 : R) ^ Module.finrank R B) *
          (LinearMap.polyCharpoly (Algebra.lmul R B).toLinearMap b).coeff 0) =
      Algebra.norm A (∑ i, (x i) ⊗ₜ[R] (b i) : A ⊗[R] B) := by
  classical
  have : Module.Free A (A ⊗[R] B) := Module.Free.of_basis (TensorProduct.basis A b)
  have : Module.Finite A (A ⊗[R] B) := Module.Finite.of_basis (TensorProduct.basis A b)
  nontriviality A
  have : Nontrivial R := (algebraMap R A).domain_nontrivial
  have hrank : Module.finrank R B = Module.finrank A (A ⊗[R] B) := by
    rw [Module.finrank_eq_card_basis b,
      Module.finrank_eq_card_basis (TensorProduct.basis A b)]
  have hpoly := LinearMap.polyCharpolyAux_map_aeval
    (Algebra.lmul R B).toLinearMap b b A x
  have hfamily := lmul_family_baseChange (R := R) (B := B) (A := A)
  rw [← LinearMap.polyCharpolyAux_basisIndep (Algebra.lmul R B).toLinearMap b
    (Module.Free.chooseBasis R B) b] at hpoly
  change (LinearMap.polyCharpoly (Algebra.lmul R B).toLinearMap b).map
    (MvPolynomial.aeval x).toRingHom = _ at hpoly
  rw [hfamily] at hpoly
  rw [← basis_coordinates b x, Algebra.norm_apply,
    LinearMap.det_eq_sign_charpoly_coeff]
  simp only [map_mul, map_pow, map_neg, map_one, ← hrank]
  congr 1
  have hcoeff := congrArg (fun p : Polynomial A ↦ p.coeff 0) hpoly
  convert hcoeff using 1
  · simp only [Polynomial.coeff_map]
    rfl
  · rfl

end
end Algebra
