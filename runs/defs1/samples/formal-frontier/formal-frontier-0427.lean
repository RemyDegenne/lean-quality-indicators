@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

variable (K Γ R : Type u)

variable [CommRing K] [CommRing R] [Algebra K R] [Fintype Γ] [Group Γ]

/-- Evaluation at any point is a multiplicative equivalence from locally
constant functions on a connected space to their target group. -/
noncomputable def locallyConstantMulEquivOfConnected
    (X Γ : Type*) [TopologicalSpace X] [ConnectedSpace X] [Group Γ] :
    LocallyConstant X Γ ≃* Γ where
  toFun f := f (Classical.choice (inferInstance : Nonempty X))
  invFun := LocallyConstant.const X
  left_inv f := by
    let x₀ : X := Classical.choice (inferInstance : Nonempty X)
    ext x
    let U : Set X := {y | f y = f x₀}
    rcases (connectedSpace_iff_clopen.mp (by infer_instance)).2 U
        (f.isLocallyConstant.isClopen_fiber (f x₀)) with hU | hU
    · have hx₀ : x₀ ∈ U := rfl
      rw [hU] at hx₀
      exact False.elim hx₀
    · have hx : x ∈ U := by rw [hU]; trivial
      exact hx.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

end AlgebraicGeometry
end
