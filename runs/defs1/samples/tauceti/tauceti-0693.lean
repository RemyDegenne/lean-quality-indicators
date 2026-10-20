public noncomputable section

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace NormalLayer

section Compositum

variable (L : NormalLayer G) (W : OpenSubgroup G)

variable (F : Formation G)

/-- The **corestriction** `A^{U ⊓ W} / N_{(U ⊓ W)/(V ⊓ W)}(A^{V ⊓ W}) → A^U / N_{U/V}(A^V)` of norm
quotients from the compositum, induced by `N_{U/(U ⊓ W)} : A^{U ⊓ W} → A^U`, which carries norms
of the compositum to norms of the layer by transitivity of norms. -/
def normQuotientCor : (L.compositum W).NormQuotient F →ₗ[ℤ] L.NormQuotient F :=
  Submodule.mapQ _ _ (F.levelNorm (L.compositum_ground_le W)).toIntLinearMap fun y hy ↦ by
    obtain ⟨b, rfl⟩ := ((L.compositum W).mem_normSubgroup F).1 hy
    refine Submodule.mem_comap.2 ((L.mem_normSubgroup F).2
      ⟨F.levelNorm (L.compositum_top_le W) b, ?_⟩)
    -- Norm transitivity identifies both composites with the norm from `V ⊓ W` to `U`.
    have hL := DFunLike.congr_fun (L.toAddMonoidHom_norm F)
      (F.levelNorm (L.compositum_top_le W) b)
    have hC := DFunLike.congr_fun ((L.compositum W).toAddMonoidHom_norm F) b
    simp only [LinearMap.toAddMonoidHom_coe] at hL hC
    rw [hL, hC, AddMonoidHom.coe_toIntLinearMap, ← AddMonoidHom.comp_apply,
      ← AddMonoidHom.comp_apply, ← Formation.levelNorm_trans, ← Formation.levelNorm_trans]

end Compositum
end NormalLayer
end TauCeti.ClassFieldTheory
end
