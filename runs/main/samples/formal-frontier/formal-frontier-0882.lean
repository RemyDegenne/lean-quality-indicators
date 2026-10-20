public section

open scoped nonZeroDivisors

universe u v

namespace ClassGroup

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B]

theorem isPrincipalIdealRing_of_generator_of_isLocalization
    (M : Submonoid A) [IsLocalization M B]
    (g : ClassGroup A) (hgen : ∀ x : ClassGroup A, x ∈ Subgroup.zpowers g)
    (hkill : ClassGroup.extendedHom A B g = 1) : IsPrincipalIdealRing B := by
  have htrivial : ∀ x : ClassGroup A, ClassGroup.extendedHom A B x = 1 := by
    intro x
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
    rw [map_zpow, hkill, one_zpow]
  have htarget : ∀ y : ClassGroup B, y = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := extendedHom_surjective_of_isLocalization M y
    exact htrivial x
  refine ⟨fun I ↦ ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]
    exact bot_isPrincipal
  · exact (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hI)).mp
      (htarget (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩))

end ClassGroup
end
