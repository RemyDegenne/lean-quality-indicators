public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs

open CFSG.LieType.BorelTits

section Cast

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f p : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

theorem normOmegaConj_castEquiv_normOmegaCast {r r' : ℕ} (h : r ≤ r')
    {g : ((F × F) × (Fin r → K)) ≃ₗ[F] ((F × F) × (Fin r → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r)) (y : normOmega E r) :
    normOmegaConj E (castEquiv_mem_orthogonalGroup E h hg) (normOmegaCast E h y) =
      normOmegaCast E h (normOmegaConj E hg y) := by
  apply Subtype.ext
  rw [normOmegaConj_apply, normOmegaCast_apply, normOmegaCast_apply, normOmegaConj_apply]
  have hmul : castEquiv h (g * (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
      ((F × F) × (Fin r → K))) * g⁻¹) =
      castEquiv h g * castEquiv h (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
        ((F × F) × (Fin r → K))) * (castEquiv h g)⁻¹ := by
    change castHom h (g * (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
        ((F × F) × (Fin r → K))) * g⁻¹) =
      castHom h g * castHom h (y : ((F × F) × (Fin r → K)) ≃ₗ[F]
        ((F × F) × (Fin r → K))) * (castHom h g)⁻¹
    simp only [map_mul, map_inv]
  rw [hmul]

end Cast
end CFSG.StandardType
end
