set_option warningAsError true

@[expose] public section

open Function

open scoped Matrix

namespace Bass

universe u

/-- The coordinate hyperplane where the `i`th coordinate vanishes is the
function module on the remaining indices. This specializes mathlib's
equivalence for intersections of kernels of coordinate projections. -/
noncomputable def coordinateHyperplaneEquiv
    (R : Type u) [Semiring R] (n : ℕ) (i : Fin n) :
    LinearMap.ker (LinearMap.proj i : (Fin n → R) →ₗ[R] R) ≃ₗ[R]
      ({j : Fin n // j ≠ i} → R) := by
  classical
  let e := LinearMap.iInfKerProjEquiv R (fun _ : Fin n ↦ R)
    (I := {j | j ≠ i}) (J := {i})
    (by
      rw [Set.disjoint_left]
      intro j hjI hjJ
      exact hjI (Set.mem_singleton_iff.mp hjJ))
    (by
      intro j _
      by_cases h : j = i
      · exact Or.inr (Set.mem_singleton_iff.mpr h)
      · exact Or.inl h)
  exact (LinearEquiv.ofEq _ _ (by simp)).trans e

end Bass
end
