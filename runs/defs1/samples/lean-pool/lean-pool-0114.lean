@[expose] public section

open scoped ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

section

variable (q : V → ℝ)

variable (hq_smul : ∀ (c : ℂ) (x : V), q (c • x) = ‖c‖ ^ 2 * q x)

variable (hq_para : ∀ x y : V,
  q (x + y) + q (x - y) = (q x + q x) + (q y + q y))

include hq_smul

omit hq_smul

include hq_para

include hq_smul

omit hq_para

include hq_para

variable (hq_nonneg : ∀ x : V, 0 ≤ q x)

include hq_nonneg

variable (hq_le : ∀ x : V, q x ≤ ‖x‖ ^ 2)

include hq_le

omit hq_para hq_nonneg hq_le

include hq_para hq_nonneg hq_le

/-- The sesquilinear map obtained by polarizing the quadratic function. -/
noncomputable def polarizationLinearMap :
    V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (complexPolarization q)
    (by exact complexPolarization_add_left q hq_smul hq_para)
    (by exact complexPolarization_smul_left q hq_smul hq_para hq_nonneg hq_le)
    (by exact complexPolarization_add_right q hq_smul hq_para)
    (by exact complexPolarization_smul_right q hq_smul hq_para hq_nonneg hq_le)

end
end
