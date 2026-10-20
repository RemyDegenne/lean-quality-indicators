set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

variable (X : TopRep.{max v w} k G)

variable {A B C : TopRep.{max v w} k G}

lemma homogeneousOne_mem_ker (f : continuousCrossedHom X) :
    ⟨homogeneousOne X f, homogeneousOne_mem_invariants X f⟩ ∈
      ((TopRep.homogeneousCochains X).d 1 2).hom.ker := by
  rw [LinearMap.mem_ker, Subtype.ext_iff, ContinuousLinearMap.coe_coe,
    TopRep.homogeneousCochains.d_apply]
  apply ContinuousMap.ext
  intro g
  apply ContinuousMap.ext
  intro h
  apply ContinuousMap.ext
  intro j
  change X.ρ h (f.1 (h⁻¹ * j)) -
    (X.ρ g (f.1 (g⁻¹ * j)) - X.ρ g (f.1 (g⁻¹ * h))) = 0
  have hf : f.1 (g⁻¹ * j) =
      X.ρ (g⁻¹ * h) (f.1 (h⁻¹ * j)) + f.1 (g⁻¹ * h) := by
    simpa [mul_assoc] using f.2 (g⁻¹ * h) (h⁻¹ * j)
  have haction (y : X) : X.ρ g (X.ρ (g⁻¹ * h) y) = X.ρ h y := by
    calc
      _ = (X.ρ g * X.ρ (g⁻¹ * h)) y := (mul_apply_eq_comp _ _ _).symm
      _ = X.ρ (g * (g⁻¹ * h)) y := by rw [← map_mul X.ρ]
      _ = _ := by simp
  have hf' := congrArg (fun y : X => X.ρ g y) hf
  rw [map_add, haction] at hf'
  rw [hf']
  abel

end ContinuousCohomology
end
