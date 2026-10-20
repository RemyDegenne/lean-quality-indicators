@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra.RightComoduleHom

section CommSemiring

variable {K : Type u} {C : Type v} {M : Type w} {N : Type*}

variable [CommSemiring K] [AddCommMonoid C] [Module K C] [Coalgebra K C]

variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]

variable {X : RightComodule K C M} {Y : RightComodule K C N}

theorem coefficientSpan_le_of_surjective (f : RightComoduleHom X Y)
    (hf : Function.Surjective f) : Y.coefficientSpan ≤ X.coefficientSpan := by
  apply (Y.coefficientSpan_le_iff _).mpr
  intro ell n
  obtain ⟨m, rfl⟩ := hf n
  rw [f.coefficient_apply]
  exact X.coefficient_mem_coefficientSpan (ell.comp f.toLinearMap) m

end CommSemiring
end Coalgebra.RightComoduleHom
end
