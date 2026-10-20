public section

open MeasureTheory Metric MulAction Set Filter

open scoped Pointwise Topology

namespace TauCeti

variable (G : Type*) {X : Type*} [PseudoMetricSpace X]

variable {G} [Group G] [MulAction G X]

variable [IsIsometricSMul G X]

variable [ProperSpace X] [ProperlyDiscontinuousSMul G X]

theorem isFundamentalDomain_dirichletDomain [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {p : X} (hp : stabilizer G p = ⊥)
    (hμ : ∀ g h : G, g • p ≠ h • p → μ {x | dist x (g • p) = dist x (h • p)} = 0) :
    IsFundamentalDomain G (dirichletDomain G p) μ where
  nullMeasurableSet := (measurableSet_dirichletDomain G p).nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall (exists_smul_mem_dirichletDomain p)
  aedisjoint g h hgh := by
    have hsub : dirichletDomain G (g • p) ∩ dirichletDomain G (h • p) ⊆
        {x | dist x (g • p) = dist x (h • p)} := by
      simpa [smul_smul] using dirichletDomain_inter_dirichletDomain_smul_subset (g • p) (h * g⁻¹)
    rw [Function.onFun, AEDisjoint, smul_dirichletDomain, smul_dirichletDomain]
    refine measure_mono_null hsub (hμ g h fun hgp ↦ hgh ?_)
    have hmem : h⁻¹ * g ∈ stabilizer G p := by
      rw [mem_stabilizer_iff, mul_smul, hgp, inv_smul_smul]
    rw [hp, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm

end TauCeti
end
