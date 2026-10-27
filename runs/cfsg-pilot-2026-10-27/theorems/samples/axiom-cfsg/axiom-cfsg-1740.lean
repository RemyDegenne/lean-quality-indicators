public section

namespace CFSG.ASVolI

open CFSG.Open

section LnFam

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem burnsideA26_isProjFieldAut {n : ℕ} {S : Type} [Group S] {K : Type} [Field K]
    (e : S ≃* StatedProj (StatedSL n K)) (σ : K ≃+* K) :
    ChA.IsProjFieldAut (StatedSL n K) σ
      (MulAut.congr e (MulAut.congr (e.trans (burnsideA26_statedToProjSL n K)).symm
        (fieldAut n K σ))) := by
  intro g
  obtain ⟨u, hu⟩ := (specialLinearGroupEquivStatedSL n K).surjective g
  refine ⟨specialLinearGroupEquivStatedSL n K (Matrix.SpecialLinearGroup.map σ.toRingHom u),
    ?_, ?_⟩
  · rw [← hu]
    apply Units.ext
    rfl
  · rw [burnsideA26_congr_trans_apply, ← hu, burnsideA26_statedToProjSL_mk, fieldAut_proj,
      burnsideA26_statedToProjSL_symm_proj]

end LnFam
end CFSG.ASVolI
end
