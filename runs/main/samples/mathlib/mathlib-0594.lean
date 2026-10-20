public section

universe u

variable (R₀ R : Type*) (M : Type u) [Ring R₀] [Ring R] [Module R₀ R]
  [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]

@[stacks 00JB "A ring is Artinian if and only if it has finite length as a module over itself."]
theorem isArtinianRing_iff_isFiniteLength : IsArtinianRing R ↔ IsFiniteLength R R :=
  ⟨fun h ↦ ((IsArtinianRing.tfae R R).out 3 4).mp h,
    fun h ↦ (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2⟩

end
