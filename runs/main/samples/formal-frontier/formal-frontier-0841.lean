public section

open scoped nonZeroDivisors

universe u v

namespace ClassGroup

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

theorem extendedHom_surjective_of_isLocalization
    (M : Submonoid A) [IsLocalization M B] :
    Function.Surjective (ClassGroup.extendedHom A B) := by
  intro c
  obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
  let I : Ideal A := J.1.under A
  have hI : I ≠ ⊥ := by
    intro hI
    have hJ : J.1 = ⊥ := by
      rw [← IsLocalization.map_under M B J.1,
        show J.1.under A = ⊥ from by simpa [I] using hI]
      exact Ideal.map_bot
    exact (mem_nonZeroDivisors_iff_ne_zero.mp J.2) hJ
  let I₀ : (Ideal A)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩
  refine ⟨ClassGroup.mk0 I₀, ?_⟩
  rw [ClassGroup.extendedHom_mk0]
  congr 1
  exact Subtype.ext (IsLocalization.map_under M B J.1)

end ClassGroup
end
