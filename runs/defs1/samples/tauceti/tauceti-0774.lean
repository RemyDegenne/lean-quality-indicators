public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u v

namespace TauCeti

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {C : Set X} {D : Set Y}
  [CWComplex C] [CWComplex D]

section

variable [RelCWComplex.Finite C] [RelCWComplex.Finite D]

/-- **The product of two finite CW complexes.**  The `n`-cells of `C ×ˢ D` are the pairs of a
`p`-cell of `C` and a `q`-cell of `D` with `p + q = n` (`TauCeti.cellProdEquiv`), and the
characteristic map of such a pair is the product of the characteristic maps after the isometry
`Fin.appendIsometryOfEq : (Fin p → ℝ) × (Fin q → ℝ) ≃ᵢ (Fin n → ℝ)`. -/
@[instance_reducible]
def cwComplexProd : CWComplex (C ×ˢ D) :=
  CWComplex.mkFinite (C ×ˢ D) (ProdCell C D) (fun _ c ↦ prodCellMap c)
    eventually_isEmpty_prodCell finite_prodCell
    (fun _ c ↦ by
      rw [prodCellMap, Equiv.transPartialEquiv_source, PartialEquiv.prod_source, source_eq,
        source_eq, ball_prod_same, ← Prod.zero_eq_mk, ← prodCellIsometry_zero c]
      exact ((prodCellIsometry c).preimage_ball _ _).trans
        (by rw [IsometryEquiv.symm_apply_apply]))
    (fun _ c ↦ ((continuousOn _ c.2.1).prodMap (continuousOn _ c.2.2)).comp
      (prodCellIsometry c).continuous.continuousOn fun _ ↦ prodCellIsometry_mem_closedBall c)
    (fun _ c ↦ (prodCellIsometry c).symm.continuous.comp_continuousOn
      ((continuousOn_symm _ c.2.1).prodMap (continuousOn_symm _ c.2.2)))
    pairwiseDisjoint_prodCellMap mapsTo_prodCellMap iUnion_prodCellMap

end
end TauCeti
end
end
