public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}

variable [Field k] [Field F] [Field F'] [Algebra k F'] [Algebra F F']

section InertiaField

variable (F) (P : Place k F')

variable [Algebra k F] [IsScalarTower k F F']

variable [FiniteDimensional F F']

variable [IsGalois F F']

theorem eq_of_restrict_inertiaField_eq {Q : Place k F'}
    (h : restrict k (inertiaField F P) Q = restrict k (inertiaField F P) P) : Q = P := by
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_restrict_eq (F := (inertiaField F P : Type v')) h
  rw [← smul_left_cancel_iff (τ.restrictScalars F), restrictScalars_smul _ τ Q, hτ,
    restrictScalars_smul_eq_self_of_inertiaField F P τ]

end InertiaField
end Place
end TauCeti
end
