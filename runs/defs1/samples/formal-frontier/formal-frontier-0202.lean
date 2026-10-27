@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- The orientation-fixed coordinate homeomorphism from the equator to the
metric unit circle in `E2`: `(x,y,0)` is sent to `(x,y)`. -/
noncomputable def sphere2EquatorHomeomorphSphere1 :
    sphere2Equator ≃ₜ (sphere1 : Type) where
  toFun p := ⟨sphere2EquatorToCircleVector p,
    mem_sphere_zero_iff_norm.mpr (sphere2EquatorToCircleVector_norm p)⟩
  invFun p := ⟨⟨sphere1ToSphere2EquatorVector p,
    mem_sphere_zero_iff_norm.mpr (sphere1ToSphere2EquatorVector_norm p)⟩,
    sphere1ToSphere2EquatorVector_third p⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphere2EquatorToCircleVector,
      sphere1ToSphere2EquatorVector, p.2]
  right_inv p := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [sphere2EquatorToCircleVector,
      sphere1ToSphere2EquatorVector]
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold sphere2EquatorToCircleVector
    apply (PiLp.continuous_toLp 2 _).comp
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    unfold sphere1ToSphere2EquatorVector
    apply (PiLp.continuous_toLp 2 _).comp
    fun_prop

end SphereTopology
end
end
