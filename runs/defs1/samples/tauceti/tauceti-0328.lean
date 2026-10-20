public section

open Opposite

namespace TauCeti

universe u v w

open GradedLinearQuiver

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- The **opposite** of an `A∞` category: the `A∞` category on the opposite quiver `Cᵒᵖ` whose
operation of arity `n` on homogeneous inputs of degrees `d` is `(-1) ^ opExp n d` times the
operation of `𝒞` on the reversed inputs.  It is the opposite of the total `A∞` algebra of `𝒞`,
transported to the total module of morphisms of `Cᵒᵖ`. -/
noncomputable def op : AInfinityCategory R Cᵒᵖ where
  __ := 𝒞.toAInfinityAlgebra.op.map (opTotalHomEquiv R C)
  grading_eq := by
    rw [AInfinityAlgebra.map_grading, AInfinityAlgebra.op_grading, 𝒞.grading_eq,
      totalGrading_map_opTotalHomEquiv]
  isPathCompatible_m_of_pos n _ := by
    have hr := (𝒞.isPathCompatible_m n).reverse
    refine isPathCompatible_of_homogeneous (fun X x d hx ↦ ?_) fun s t x d hx i j hij hne ↦ ?_
    · rw [𝒞.opMap_m_apply (fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) _ fun i ↦ by simpa using hx i]
      exact Submodule.smul_mem _ _ (hr.mem_range_homInclusion X x)
    · rw [𝒞.opMap_m_apply (fun k ↦ if h : k < n then d ⟨k, h⟩ else 0) _ fun i ↦ by simpa using hx i,
        hr.eq_zero_of_ne s t x i j hij hne, smul_zero]

end AInfinityCategory
end TauCeti
end
