namespace OAI

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

section Concrete

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N : VonNeumannAlgebra H}

local instance descentOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _

local instance descentOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

local instance descentFactorOrder (P : VonNeumannAlgebra H) : PartialOrder (Algebra P) :=
  CStarAlgebra.spectralOrder _

local instance descentFactorStarOrder (P : VonNeumannAlgebra H) : StarOrderedRing (Algebra P) :=
  CStarAlgebra.spectralOrderedRing _

theorem concrete_unitary_of_retracted_conjugation
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (j : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (hj : Function.Injective j)
    (E : (K →L[ℂ] K) →CP (H →L[ℂ] H)) (hE : E 1 = 1)
    (hfix : ∀ x, E (j x) = x)
    (z : unitary (K →L[ℂ] K))
    (hmem : ∀ x : Algebra M,
      E ((z : K →L[ℂ] K) * j x * star (z : K →L[ℂ] K)) ∈ N)
    {g : ℝ} (hgap : kkDistance M N < g)
    (hsmall : 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1 / 1000)
    (hge : g + 2 * ‖(z : K →L[ℂ] K) - 1‖ < 1) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ 256 * ‖(z : K →L[ℂ] K) - 1‖ := by
  let ρ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K) :=
    (Unitary.conjStarAlgAut ℂ (K →L[ℂ] K) z).toStarAlgHom.comp
      (j.comp (algebraInclusion M))
  let F : Algebra M →CP (H →L[ℂ] H) :=
    completelyPositiveComp E (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ)
  let L : Algebra M →ₗ[ℂ] Algebra N :=
    F.toLinearMap.codRestrict N.toStarSubalgebra.toSubmodule (fun x => by
      change E (ρ x) ∈ N
      exact hmem x)
  let φ : Algebra M →CP Algebra N :=
    completelyPositive_of_embedding (algebraInclusion N) Subtype.val_injective F L
      (fun _ => rfl)
  have hφ : φ 1 = 1 := by
    apply Subtype.ext
    change E (ρ 1) = 1
    rw [map_one, hE]
  have hfull := retracted_conjugation_complete_bound j hj E hE hfix z
  have hrestricted := completelyBoundedBy_comp_completeIsometry _
    (algebraInclusion M).toAlgHom.toLinearMap hfull
    (injective_starAlgHom_completelyIsometric (algebraInclusion M) Subtype.val_injective)
  have hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap)
      (2 * ‖(z : K →L[ℂ] K) - 1‖) := by
    convert hrestricted using 1
    ext x
    rfl
  obtain ⟨u, hu, hnorm⟩ := concrete_ucp_unitary_of_published hCorrection hCommutant φ hφ
    (by positivity) hsmall hge hclose hgap
  refine ⟨u, hu, ?_⟩
  linarith

end Concrete
end
end KadisonKastler
end OAI
