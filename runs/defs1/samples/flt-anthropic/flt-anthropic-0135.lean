namespace P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace EtaleEdgeChart

section Coordinates

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

variable (𝒪 K) in

noncomputable def coord (i : Fin 2) : ↥(stdFullLattice (𝒪 := 𝒪) K).1 →ₗ[𝒪] 𝒪 where
  toFun v := (isInteger_apply v i).choose
  map_add' v w := by
    apply IsFractionRing.injective 𝒪 K
    rw [(isInteger_apply (v + w) i).choose_spec, map_add, (isInteger_apply v i).choose_spec,
      (isInteger_apply w i).choose_spec]
    rfl
  map_smul' r v := by
    apply IsFractionRing.injective 𝒪 K
    rw [(isInteger_apply (r • v) i).choose_spec, RingHom.id_apply, smul_eq_mul, map_mul,
      (isInteger_apply v i).choose_spec]
    show ((r • (v : Fin 2 → K)) i) = _
    rw [Pi.smul_apply, Algebra.smul_def]

end Coordinates
end EtaleEdgeChart
end P2MW.S_CerednikDrinfeld_QM_etale_edgeChartMorphism_of_cerednikDrinfeld_uniformization_fine
