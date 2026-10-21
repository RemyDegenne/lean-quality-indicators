namespace OAI

section

section

section

section

noncomputable section

open scoped commutatorElement

open _root_.Polynomial _root_.OAI.Polynomial

namespace SquareInduction

open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters RationalTailCoordinates

open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevHorizontal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma degree_integer_linear_return [TopologicalSpace G] [IsTopologicalGroup G]
    (s : ℕ) (hs1 : 1 ≤ s) (f : ℤ→G) (γ : G) (ξ : G→*Multiplicative ℝ)
    (a : ℤ) (ha : (ξ γ).toAdd=(a:ℝ)) (P : ℝ[X]) (hP : P.natDegree ≤ s)
    (hPe : ∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z*(γ^z)⁻¹)).toAdd)
    (A : ℝ) (N : ℕ)
    (hPc : ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j) :
    ∃ Q : ℝ[X], Q.natDegree ≤ s ∧ (∀ z : ℤ, Q.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
      ∀ j : ℕ, 0<j → ∃ z : ℤ, |Q.coeff j-z| ≤ A/(N:ℝ)^j := by
  refine ⟨P+C (a:ℝ)*X,?_,?_,?_⟩
  · exact natDegree_add_le_of_degree_le hP ((natDegree_C_mul_le _ _).trans (by simpa using hs1))
  · intro z
    simp only [eval_add,eval_mul,eval_C,eval_X,hPe,map_mul,map_inv,map_zpow,
      toAdd_mul,toAdd_inv,toAdd_zpow,
      zsmul_eq_mul,ha]
    ring
  · intro j hj
    obtain ⟨z,hz⟩ := hPc j hj
    by_cases he : j=1
    · subst j
      refine ⟨z+a,?_⟩
      simpa only [coeff_add,coeff_C_mul,coeff_X_one,mul_one,Int.cast_add,add_sub_add_right_eq_sub] using hz
    · refine ⟨z,?_⟩
      simpa [coeff_add,coeff_C_mul,coeff_X,he,Ne.symm he] using hz

end SquareInduction
end
end
end
end
end
end OAI
