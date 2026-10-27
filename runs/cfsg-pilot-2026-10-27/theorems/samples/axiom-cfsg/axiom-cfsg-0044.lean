public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec10

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

namespace Config

variable {Rs X Y : Subgroup G}

theorem not_isQDGroup (hc : Config σ r Rs X Y) (hσ : σ.IsValid) (hF : σ.ChapterIIFacts)
    (Δ : Data σ r) : ¬ IsQDGroup (Subgroup.normalizer (Rs : Set G)) := by
  refine hF.not_qd_of_cover _ (hc.T_le_H hσ) (hc.oddCoreIn_ne_bot Δ) ?_
  intro g hg
  exact ⟨g, hc.C_le hg.1, 1, (σ.C ⊓ σ.ON).one_mem, mul_one g⟩

end Config
end CFSG.ABGTheoremB.TotallyInverted.Sec10
end
