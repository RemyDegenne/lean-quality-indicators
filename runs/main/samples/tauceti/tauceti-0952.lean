public section

open scoped TensorProduct

open Algebra.TensorProduct (includeRight)

namespace Ideal

section CommRing

variable {K : Type*} [CommRing K] {A : Type*} [CommRing A] [Algebra K A]

theorem eq_map_comap_includeRight_of_isDomain {E : Type*} [CommRing E] [Algebra K E]
    (Q : Ideal (E ⊗[K] A)) {I : Ideal A} (hQ : Q ∈ (I.map includeRight).minimalPrimes)
    (hdom : IsDomain (E ⊗[K] (A ⧸ Q.comap includeRight))) :
    Q = (Q.comap includeRight).map includeRight := by
  have hPQ : (Q.comap includeRight).map includeRight ≤ Q := Ideal.map_le_iff_le_comap.mpr le_rfl
  refine Minimal.eq_of_ge (P := fun J : Ideal (E ⊗[K] A) ↦ J.IsPrime ∧ I.map includeRight ≤ J)
    hQ ⟨?_, ?_⟩ hPQ
  · -- `(E ⊗[K] A) ⧸ P.map includeRight` is `E ⊗[K] (A ⧸ P)`, a domain.
    have := (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K A E (Q.comap includeRight)).symm
      |>.toMulEquiv.isDomain
    exact Ideal.Quotient.isDomain_iff_prime _ |>.mp this
  · exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mp hQ.le)

end CommRing
end Ideal
end
