@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Coalgebra

section CommSemiring

variable (R : Type u) (C : Type v)

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

@[simp] theorem counit_range_eq_top_of_free [Module.Free R C] [Nontrivial C] :
    (LinearMap.range (counit (R := R) (A := C)) : Ideal R) = ⊤ := by
  classical
  let b := Module.Free.chooseBasis R C
  let i : Module.Free.ChooseBasisIndex R C := Classical.choice inferInstance
  have hcoord : LinearMap.range (b.coord i) = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro r
    refine ⟨r • b i, ?_⟩
    simp [Module.Basis.coord_apply]
  have h := congrArg (Submodule.map (b.coord i)) (counit_range_smul_top R C)
  rw [Submodule.map_smul'', Submodule.map_top, hcoord, Ideal.smul_eq_mul,
    Ideal.mul_top] at h
  exact h

end CommSemiring
end Coalgebra
end
