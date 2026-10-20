public section

open IntermediateField

namespace TauCeti

open AlgebraicGeometry

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem Divisor.exists_mem_dim_sub_ofPoint_lt (hF : IsFunctionField k F) {D : Divisor k F}
    {T : Finset (Place k F)} (hD : 0 < Divisor.dim D)
    (hdeg : Divisor.degree D + Module.finrank k (algebraicClosure k F) <
      Divisor.dim D + ∑ P ∈ T, (P.degree : ℤ)) :
    ∃ P ∈ T, Divisor.dim (D - WeilDivisor.ofPoint P) < Divisor.dim D := by
  by_contra! h
  have := finiteDimensional_riemannRochSpace hF D
  have heq : riemannRochSpace (D - WeilDivisor.ofFinset T) = riemannRochSpace D :=
    riemannRochSpace_sub_ofFinset_eq fun P hP ↦
      Submodule.eq_of_le_of_finrank_le
        (riemannRochSpace_mono (sub_le_self _ (WeilDivisor.isEffective_iff_zero_le.mp
          (WeilDivisor.isEffective_ofPoint P))))
        (by rw [← Divisor.dim_def, ← Divisor.dim_def]; exact h P hP)
  have hne : riemannRochSpace (D - WeilDivisor.ofFinset T) ≠ ⊥ := by
    rw [heq, ← Divisor.one_le_dim_iff_riemannRochSpace_ne_bot hF]
    exact hD
  have hle := Divisor.dim_le_degree_add_finrank_of_riemannRochSpace_ne_bot hF hne
  rw [Divisor.dim_def, heq, ← Divisor.dim_def, Divisor.degree_sub,
    Divisor.degree_eq_weightedDegree (WeilDivisor.ofFinset T),
    WeilDivisor.weightedDegree_ofFinset] at hle
  omega

end TauCeti
end
