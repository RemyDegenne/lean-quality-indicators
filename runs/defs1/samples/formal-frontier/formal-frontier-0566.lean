set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

/-- Evaluation at the identity identifies homogeneous degree-zero cochains
with their coefficient representation when the represented action is jointly
continuous. -/
@[expose]
def cochainsZeroEquiv [TopRep.JointlyContinuous X] :
    (TopRep.homogeneousCochains X).X 0 ≃L[k] X where
  toFun σ := σ.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨orbitMap X x, by
        intro g
        apply DFunLike.ext _ _
        intro h
        simp only [ContRepresentation.coind₁_apply_apply, orbitMap,
          ContinuousLinearMap.coe_mk']
        change X.ρ g (X.ρ (g⁻¹ * h) x) = X.ρ h x
        calc
          _ = (X.ρ g * X.ρ (g⁻¹ * h)) x :=
            (mul_apply_eq_comp _ _ _).symm
          _ = X.ρ (g * (g⁻¹ * h)) x := by
            rw [← map_mul X.ρ g (g⁻¹ * h)]
          _ = _ := by simp⟩
  left_inv σ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    change X.ρ g (σ.1 1) = σ.1 g
    simpa [ContRepresentation.coind₁_apply_apply] using DFunLike.congr_fun (σ.2 g) g
  right_inv x := by
    change X.ρ 1 x = x
    simp
  continuous_toFun := (continuous_eval_const 1).comp continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 (orbitMap X).continuous

end ContinuousCohomology
end
