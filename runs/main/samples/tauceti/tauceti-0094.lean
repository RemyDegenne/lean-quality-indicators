public section

namespace TauCeti

open GradedLinearQuiver GradedLinearQuiver.InducedQuiver

universe u₁ u₂ v₁ v₂ w

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]
  {𝒷 : AInfinityCategory R C} {𝒸 : AInfinityCategory R D}

namespace AInfinityFunctor

variable (ℱ : AInfinityFunctor 𝒷 𝒸)

@[simp]
theorem component_zero (X : Fin 1 → C) : ℱ.component X = 0 := by
  apply MultilinearMap.ext
  intro f
  apply homInclusion_injective (C := InducedQuiver D ℱ.obj) ⟨X 0⟩ ⟨X (Fin.last 0)⟩
  rw [homInclusion_component, AInfinityHom.component_zero]
  simp

end AInfinityFunctor
end TauCeti
end
