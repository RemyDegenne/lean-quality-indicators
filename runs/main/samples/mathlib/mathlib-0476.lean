public section

universe u v w w₁ w₂

namespace LieIdeal

open LieAlgebra

variable {R : Type u} {L : Type v} {L' : Type w₂}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

variable {f}

theorem map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ := by
  rw [← map_sup_ker_eq_map, ← comap_bracket_eq h, map_comap_eq h, inf_eq_right]
  exact le_trans (LieSubmodule.lie_le_left _ _) inf_le_left

end LieIdeal
end
