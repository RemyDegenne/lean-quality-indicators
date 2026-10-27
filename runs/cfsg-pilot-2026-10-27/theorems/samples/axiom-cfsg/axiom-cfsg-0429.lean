public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Module

variable {F : Type*} [Field F] {k m : ℕ}

section Block

variable (A D : (Fin k → F) →ₗ[F] (Fin k → F)) (K : (Fin m → F) →ₗ[F] (Fin m → F))
  (B : (Fin m → F) →ₗ[F] (Fin k → F)) (C : (Fin k → F) →ₗ[F] (Fin m → F))

variable {A K} in
theorem nilBlockMap_injective (hA : Function.Injective A) (hK : Function.Injective K) :
    Function.Injective (nilBlockMap A D K B C) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, z, y⟩ h
  simp only [nilBlockMap_apply, Prod.mk_eq_zero] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx : x = 0 := hA (by rw [h1, map_zero])
  subst hx
  rw [map_zero, zero_add] at h2
  have hz : z = 0 := hK (by rw [h2, map_zero])
  subst hz
  rw [map_zero, map_zero, zero_add, zero_add] at h3
  have hy : y = 0 := hA (by rw [h3, map_zero])
  subst hy
  rfl

end Block
end CFSG.LargeExtraspecial.GLR
end
