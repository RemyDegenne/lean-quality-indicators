namespace P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero

set_option autoImplicit false

namespace SmoothPointDVR

open MvPolynomial

section Local

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x y : F} {f : MvPolynomial (Fin 2) K} {a b : K}
  (hker : ∀ g : MvPolynomial (Fin 2) K, aeval ![x, y] g = 0 → g ∈ Ideal.span {f})
  (hab : eval ![a, b] f = 0)

scoped instance 𝔮_isPrime : (𝔮 hker hab).IsPrime := RingHom.ker_isPrime _

theorem primeCompl_le_nonZeroDivisors : (𝔮 hker hab).primeCompl ≤ nonZeroDivisors (A K x y) := by
  intro z hz
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hz (Ideal.zero_mem _)

end Local
end SmoothPointDVR
end P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero
