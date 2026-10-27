public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

/-- The identity-on-points homeomorphism from the chart of a cone of a subfan to the chart of the
same cone in the ambient fan. -/
noncomputable def subfanAnalyticChartMap (σ : (Φ.subfan S hS hface).cones) :
    ((Φ.subfan S hS hface).analyticAffineChartDiagram).obj σ ≃ₜ
      (Φ.analyticAffineChartDiagram).obj
        ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩ where
  toEquiv := Equiv.refl _
  continuous_toFun :=
    continuous_id_iff_le.mpr (Φ.subfan_analyticAffineChartDiagram_obj_str S hS hface σ).le
  continuous_invFun :=
    continuous_id_iff_le.mpr (Φ.subfan_analyticAffineChartDiagram_obj_str S hS hface σ).ge

end TauCeti.Toric.Fan
end
