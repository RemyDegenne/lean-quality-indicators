noncomputable section

attribute [local instance low] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance low] AddSubgroupClass.instZModModule

namespace ConnesRigidity

section

open ConnesRigidity MeasureTheory

open scoped NNReal ENNReal

universe u v w

section

variable {K : Type u} [Group K]

variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]

variable {Ξ : Type w} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[expose]
public
def crossedFiberwiseOperator
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : H →L[ℂ] H) :
    lp (fun _ : K ↦ H) 2 →L[ℂ] lp (fun _ : K ↦ H) 2 := by
  let F : lp (fun _ : K ↦ H) 2 →ₗ[ℂ] lp (fun _ : K ↦ H) 2 :=
    { toFun := fun ξ ↦
        ⟨fun k ↦ T (ξ k), by
          apply ((lp.memℓp ξ).const_smul (‖T‖ : ℂ)).mono'
          intro k
          change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
          simpa only [Complex.coe_smul, norm_smul, norm_norm] using T.le_opNorm (ξ k)⟩
      map_add' := by
        intro ξ η
        ext k
        exact map_add T (ξ k) (η k)
      map_smul' := by
        intro c ξ
        ext k
        exact map_smul T c (ξ k) }
  exact F.mkContinuous ‖T‖ (by
    intro ξ
    calc
      ‖F ξ‖ ≤ ‖(‖T‖ : ℂ) • ξ‖ := lp.norm_mono (by norm_num) (by
        intro k
        change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
        simpa only [Complex.coe_smul, norm_smul, norm_norm] using T.le_opNorm (ξ k))
      _ = ‖T‖ * ‖ξ‖ := by
        rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
        simp only [Complex.norm_real, norm_norm])

end
end
end ConnesRigidity
end
