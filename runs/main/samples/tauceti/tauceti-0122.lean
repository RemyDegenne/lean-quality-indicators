public section

open TensorProduct WithConv TauCeti

namespace TauCeti.Cocharacter

variable {R S H A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

variable [Semiring H]

variable [CommSemiring A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

variable [HopfAlgebra R H]

@[simp]
theorem baseChangePointsMulEquiv_mem_unipotent_iff (l : H →ₐc[R] LaurentPolynomial R)
    (g : WithConv (H →ₐ[R] A)) :
    AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H) g ∈
        unipotent A (l.baseChangeCocharacter S) ↔
      g ∈ unipotent A l := by
  rw [mem_unipotent_iff, mem_unipotent_iff]
  constructor
  · rintro ⟨hg, hlim⟩
    have hg' := (baseChangePointsMulEquiv_mem_parabolic_iff l g).mp hg
    refine ⟨hg', (AlgHom.baseChangePointsMulEquiv (k := R) (K := S) (A := H)).injective ?_⟩
    rw [baseChangePointsMulEquiv_limit, hlim, map_one]
  · rintro ⟨hg, hlim⟩
    refine ⟨(baseChangePointsMulEquiv_mem_parabolic_iff l g).mpr hg, ?_⟩
    rw [← baseChangePointsMulEquiv_limit l ⟨g, hg⟩, hlim, map_one]

end TauCeti.Cocharacter
end
