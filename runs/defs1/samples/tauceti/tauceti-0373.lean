public section

noncomputable section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

/-- The product collar identification is smooth in both directions for Mathlib's standard models
with corners, at every finite or infinite regularity. -/
def collarDiffeomorph (n : ℕ) {k : WithTop ℕ∞} :
    Diffeomorph ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1))
      (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1) (EuclideanHalfSpace (n + 1)) k where
  toEquiv := collarEquiv n
  contMDiff_toFun := by
    rw [chartedSpaceSelf_prod]
    let I := (𝓡 n).prod (𝓡∂ 1)
    let J := 𝓡∂ (n + 1)
    have hcoord : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) k
        (collarAmbientEquiv n ∘ I) :=
      (collarAmbientEquiv n).contDiff.contMDiff.comp I.contMDiff
    have hrange : ∀ p, collarAmbientEquiv n (I p) ∈ range J := by
      intro p
      rw [range_modelWithCornersEuclideanHalfSpace]
      dsimp [I]
      rw [collarAmbientEquiv_apply_zero]
      simpa using p.2.2
    refine (J.contMDiffOn_symm.comp_contMDiff hcoord hrange).congr ?_
    intro p
    apply Subtype.ext
    -- Expand the model inverse explicitly so its half-space coercion can be rewritten by its API.
    change collarAmbientEquiv n (p.1, p.2.1) =
      ((𝓡∂ (n + 1)).symm (collarAmbientEquiv n (p.1, p.2.1))).1
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le]
    simpa only [collarAmbientEquiv_apply_zero] using p.2.2
  contMDiff_invFun := by
    rw [chartedSpaceSelf_prod]
    let I := (𝓡 n).prod (𝓡∂ 1)
    let J := 𝓡∂ (n + 1)
    have hcoord : ContMDiff J 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) k
        ((collarAmbientEquiv n).symm ∘ J) :=
      (collarAmbientEquiv n).symm.contDiff.contMDiff.comp J.contMDiff
    have hrange : ∀ y, (collarAmbientEquiv n).symm (J y) ∈ range I := by
      intro y
      rw [ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
      refine ⟨mem_range_self _, ?_⟩
      dsimp [J]
      exact collarAmbientEquiv_symm_apply_snd_apply_zero_nonneg n y
    refine (I.contMDiffOn_symm.comp_contMDiff hcoord hrange).congr ?_
    intro y
    apply I.injective
    simp only [Function.comp_apply]
    rw [I.right_inv (hrange y)]
    rw [modelWithCorners_prod_coe]
    rw [modelWithCornersEuclideanHalfSpace_apply]
    rfl

end TauCeti.EuclideanHalfSpace
end
end
