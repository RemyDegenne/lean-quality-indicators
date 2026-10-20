public section

open Filter Topology UpperHalfPlane

open scoped Manifold MatrixGroups

namespace TauCeti.UpperHalfPlane

lemma _root_.MvPolynomial.mdifferentiable_aeval_coe {R : Type*} [CommSemiring R] [Algebra R ℂ]
    (P : MvPolynomial (Fin 2) R) : MDiff fun z : ℍ ↦ MvPolynomial.aeval ![(z : ℂ), 1] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using mdifferentiable_const
  | add p q hp hq =>
    simp only [map_add]
    exact MDifferentiable.add hp hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    refine MDifferentiable.mul hp ?_
    fin_cases i
    · simpa using mdifferentiable_coe
    · simpa using mdifferentiable_const

end TauCeti.UpperHalfPlane
end
