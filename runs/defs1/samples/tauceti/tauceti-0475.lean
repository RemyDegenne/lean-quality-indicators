public section

noncomputable section

open Metric Real

open scoped unitInterval

namespace TauCeti

/-- The standard loop `I¹ → S¹`, `t ↦ (cos 2πt, sin 2πt)`. -/
def circleLoop : C(Fin 1 → I, Sphere1) where
  toFun t :=
    ⟨!₂[cos (2 * π * t 0), sin (2 * π * t 0)], by
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact cos_sq_add_sin_sq _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · simp only [Fin.zero_eta]
      fun_prop
    · simp only [Fin.mk_one]
      fun_prop

end TauCeti
end
end
