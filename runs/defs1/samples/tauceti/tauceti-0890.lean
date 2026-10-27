public section

namespace TauCeti

open CategoryTheory

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]

variable (𝒜 : ℤ → Submodule k A)

namespace GradedModuleCat

attribute [instance] isAddCommGroup isModule isModuleBase isScalarTower gradedSMul

variable {𝒜}

section Shift

variable (M : GradedModuleCat.{v} 𝒜)

/-- The graded module `M{n}`: the module `M` with `(M{n})ₚ = M_{p-n}`. -/
abbrev shiftObj (n : ℤ) : GradedModuleCat.{v} 𝒜 where
  carrier := M
  grading := M.grading.shift (-n)
  gradedSMul := ⟨fun {i j} _ _ ha hx ↦ by
    rw [InternalGrading.shift_piece] at hx ⊢
    simpa [add_assoc] using SetLike.GradedSMul.smul_mem (B := M.grading.piece) ha hx⟩

end Shift
end GradedModuleCat
end TauCeti
end
