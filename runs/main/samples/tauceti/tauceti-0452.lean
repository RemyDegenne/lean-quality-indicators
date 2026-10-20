public section

noncomputable section

open CategoryTheory MonoidalCategory Module

namespace FGModuleCat

universe u

variable (K : Type u) [Field K]

variable {K}

@[simp]
theorem leftAdjointMate_hom {V W : FGModuleCat.{u} K} (f : V ⟶ W) :
    (ᘁf).hom.hom = f.hom.hom.dualMap := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have h := congrArg
    (fun g : V ⊗ (ᘁW) ⟶ 𝟙_ (FGModuleCat K) => g.hom.hom (x ⊗ₜ[K] φ))
    (leftAdjointMate_comp_evaluation f)
  simp only [hom_hom_comp, LinearMap.comp_apply] at h
  -- The tensor maps have definitionally equal carriers hidden by the chosen-dual wrappers.
  erw [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul] at h
  erw [leftEvaluation_apply, leftEvaluation_apply] at h
  exact h

end FGModuleCat
end
end
