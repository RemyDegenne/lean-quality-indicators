set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

section SatGates

theorem gate_existsUnique_familyExtension_trivialGroupScheme_z3
    (T : ℕ → SchemeHomOver
      (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (specGenericFibreInclusion ℤ_[3] ℚ_[3]))
      (pullback.snd (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (specGenericFibreInclusion ℤ_[3] ℚ_[3]))) :
    ∃! S : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (𝟙 (Spec (CommRingCat.of ℤ_[3]))),
      ∀ j, genericFibreRestrict ℤ_[3] ℚ_[3] (𝟙 (Spec (CommRingCat.of ℤ_[3])))
        (𝟙 (Spec (CommRingCat.of ℤ_[3]))) (S j) = T j :=
  (gate_neronModelPropertyBundle_trivialGroupScheme_z3).existsUnique_familyExtension T

end SatGates
end NeronModelInfra
end
