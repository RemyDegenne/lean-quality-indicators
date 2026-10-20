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
theorem rightFreeLinearMapScalarExtension_map_comp [Fintype κ]
    (h : (κ → R) →ₗ[Rᵐᵒᵖ] (ν → R)) :
    rightFreeLinearMapScalarExtension R ι ν f (h.comp g) =
      (rightFreeLinearMapScalarExtension R κ ν f h).comp
        (rightFreeLinearMapScalarExtension R ι κ f g) := by
  apply LinearMap.pi_ext
  intro j s
  simp only [LinearMap.comp_apply, rightFreeLinearMapScalarExtension_single]
  change MulOpposite.op s • (fun i ↦ f (h (g (Pi.single j 1)) i)) =
    rightFreeLinearMapScalarExtension R κ ν f h
      (MulOpposite.op s • (fun k ↦ f (g (Pi.single j 1) k)))
  rw [map_smul, rightFreeLinearMapScalarExtension_coefficients]

end CharacteristicLaws
end Module
end
