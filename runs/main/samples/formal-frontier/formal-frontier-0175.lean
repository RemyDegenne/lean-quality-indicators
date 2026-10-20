@[expose] public section

open scoped MonoidAlgebra TensorProduct

universe u v w w'

namespace Representation

variable {R : Type u} {G : Type v} {M : Type w} {N : Type w'}
  [CommSemiring R] [Group G] [Finite G]
  [AddCommMonoid M] [Module R M]

theorem finiteFunctionTensorLinearEquiv_twisted_single
    [DecidableEq G] (ρ : Representation R G M) (g s : G) (m : M) :
    MonoidAlgebra.finiteFunctionTensorLinearEquiv R G M
        (fun t => ρ g ((Pi.single s m : G → M) (g⁻¹ * t))) =
      ρ g m ⊗ₜ[R] MonoidAlgebra.single (g * s) 1 := by
  classical
  have hfun : (fun t => ρ g ((Pi.single s m : G → M) (g⁻¹ * t))) =
      Pi.single (g * s) (ρ g m) := by
    funext t
    by_cases ht : t = g * s
    · subst t
      simp
    · have hne : g⁻¹ * t ≠ s := by
        intro h
        apply ht
        calc t = g * (g⁻¹ * t) := by simp
          _ = g * s := by rw [h]
      simp [ht, hne]
  rw [hfun]
  exact MonoidAlgebra.finiteFunctionTensorLinearEquiv_single R G M (g * s) (ρ g m)

end Representation
end
