public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

variable (R : Type u) (C : Type v) (M : Type w)

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M] [Comodule R C M]

namespace Subcomodule

variable {R C M}

theorem coact_mem_tensor_top (m : M) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range (TensorProduct.map (⊤ : Submodule R M).subtype
        (LinearMap.id : C →ₗ[R] C)) :=
  LinearMap.mem_range.mpr
    (TensorProduct.map_surjective (fun m ↦ ⟨⟨m, Submodule.mem_top⟩, rfl⟩)
      Function.surjective_id _)

end Subcomodule
end TauCeti
end
