namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem pointwiseSymbolSpanningFamily_span [Fintype (SymbolBasisIndex w ω)]
    (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hlayers) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v)) =
      (F.symbolPointwiseSubalgebra b ω hlayers w U).toSubmodule := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply F.homogeneousSymbolLift_mem_pointwise b ω hlayers w U hU
    change v z.2 ∈ U.toSubmodule
    rw [← hspan]
    exact Submodule.subset_span ⟨z.2, rfl⟩
  · intro x hx
    rw [← sum_basisBlockProjection (F.polynomialSymbolBasis b ω hlayers w) (fun z => z.val.1) x]
    apply Submodule.sum_mem
    intro α hα
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hα
    rw [← F.homogeneousSymbolLift_coefficient]
    let W := Submodule.span ℚ (Set.range (F.pointwiseSymbolSpanningFamily b ω hlayers w v))
    have hmap : U.toSubmodule ≤ W.comap (F.homogeneousSymbolLift b ω hlayers w z.val.1) := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(z, j), rfl⟩
    exact hmap ((F.mem_symbolPointwiseSubalgebra_iff b ω hlayers w U x).mp hx z.val.1)

end Erdos3.NilpotentLieFiltration
end
end OAI
