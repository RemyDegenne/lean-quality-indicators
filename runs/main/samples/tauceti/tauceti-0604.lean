public noncomputable section

namespace TauCeti.ClassFieldTheory

open NormalLayer

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Reciprocity

variable {V : OpenNormalSubgroup (AbsoluteGaloisGroup K)}

variable {K}

theorem surjective_localAbelianArtinHom (hV : V.IsAbelianClassFieldLayer) :
    Function.Surjective (localAbelianArtinHom K hV) := by
  intro γ
  obtain ⟨a, ha⟩ := (localClassFormation K).surjective_abelianArtinMap hV (Additive.ofMul γ)
  obtain ⟨x, rfl⟩ := (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
    (fixedField_toSubgroup_top_eq_fieldRange K)).surjective a
  refine ⟨x.toMul, ?_⟩
  rw [localAbelianArtinHom_apply, ofMul_toMul, ha, toMul_ofMul]

end Reciprocity
end TauCeti.ClassFieldTheory
end
