@[expose] public section

universe uR uS uT uι uκ uν

open Function

open scoped Matrix

namespace Module

section CharacteristicLaws

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Semiring R] [Semiring S] [Semiring T]

variable {ι : Type uι} {κ : Type uκ} {ν : Type uν} [Fintype ι]

variable (f : R →+* S) (g : (ι → R) →ₗ[Rᵐᵒᵖ] (κ → R))

open Classical in
@[simp]
theorem rightFreeLinearMapScalarExtension_single (j : ι) (s : S) :
    rightFreeLinearMapScalarExtension R ι κ f g (Pi.single j s) =
      fun i ↦ f (g (Pi.single j 1) i) * s := by
  funext i
  rw [rightFreeLinearMapScalarExtension_apply]
  exact dotProduct_single (fun k ↦ f (g (Pi.single k 1) i)) s j

end CharacteristicLaws
end Module
end
