set_option autoImplicit false

public section

open CategoryTheory

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

noncomputable section

namespace CorestrictionTransversal

variable {H : Subgroup G} (T : H.RightTransversal)

variable (X : TopRep.{max v w} k G)

noncomputable local instance transversalFintype (H : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] (T : H.toSubgroup.RightTransversal) :
    Fintype ↥(T : Set G) :=
  T.2.finite_right.fintype

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma rho_factor_change (S : H.RightTransversal) (t : ↥(T : Set G))
    (g : G) (x : X) :
    X.ρ ((t : G)⁻¹)
        (X.ρ (changeFactor T S t * factor S (changeRep T S t) g : H)
          (X.ρ ((changeFactor T S (next T t g) : G)⁻¹) x)) =
      X.ρ g (X.ρ ((next T t g : G)⁻¹) x) := by
  calc
    _ = X.ρ ((t : G)⁻¹)
          (X.ρ ((changeFactor T S t * factor S (changeRep T S t) g *
            (changeFactor T S (next T t g))⁻¹ : H) : G) x) := by
      apply congrArg (X.ρ ((t : G)⁻¹))
      rw [rho_mul_apply]
      rfl
    _ = X.ρ ((t : G)⁻¹) (X.ρ (factor T t g : G) x) := by
      rw [factor_change T S t g]
    _ = _ := rho_inv_factor X T t g x

end CorestrictionTransversal
end
end ContinuousCohomology
end
