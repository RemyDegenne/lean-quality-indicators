@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable {K : Type u} {Γ : Type v} {R S : Type*}

variable [CommRing K] [Fintype Γ]

namespace Points

/-- Locally constant functions on a prime spectrum are equivalent to complete
orthogonal idempotent partitions indexed by their codomain. -/
noncomputable def locallyConstantEquivIdempotentPartitions [CommRing R] :
    LocallyConstant (PrimeSpectrum R) Γ ≃ IdempotentPartitions Γ R where
  toFun f := ⟨idempotentOfLocallyConstant f, idempotentOfLocallyConstant_complete f⟩
  invFun e := locallyConstantOfIdempotents e.1 e.2
  left_inv f := by
    ext p
    apply (locallyConstantOfIdempotents_apply_eq_iff _ _ p (f p)).2
    exact (mem_basicOpen_idempotentOfLocallyConstant_iff f (f p) p).2 rfl
  right_inv e := by
    ext g
    let E := PrimeSpectrum.isIdempotentElemEquivClopens (R := R)
    let lhs : {x : R // IsIdempotentElem x} :=
      E.symm (fiberClopen (locallyConstantOfIdempotents e.1 e.2) g)
    have hsub : lhs = ⟨e.1 g, e.2.idem g⟩ := by
      apply E.injective
      rw [E.apply_symm_apply]
      apply TopologicalSpace.Clopens.ext
      ext p
      simp only [fiberClopen]
      exact locallyConstantOfIdempotents_apply_eq_iff e.1 e.2 p g
    exact congrArg Subtype.val hsub

end Points
end FiniteGroupFunctions
end AlgebraicGeometry
end
