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

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma rho_inv_changeFactor (S : H.RightTransversal) (t : ↥(T : Set G)) (x : X) :
    X.ρ ((t : G)⁻¹) (X.ρ (changeFactor T S t : G) x) =
      X.ρ ((changeRep T S t : G)⁻¹) x := by
  rw [rho_mul_apply]
  congr 2
  rw [← changeFactor_mul_changeRep T S t]
  simp

end CorestrictionTransversal
end
end ContinuousCohomology
end
