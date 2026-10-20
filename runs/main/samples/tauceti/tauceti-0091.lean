public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.Toric.FanHom

variable {N N' : Type} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (f : FanHom Φ Ψ)

@[reassoc]
theorem algebraicRealizationActionChartMap_comp_algebraicActionMap (σ : Φ.cones) :
    Fan.algebraicRealizationActionChartMap σ ≫ f.algebraicActionMap =
      affineToricSchemeActionMap Φ.lattice σ.1 Ψ.lattice f.latticeMap f.realMap
          f.map_lattice (f.mapsTo_leastCone σ.2) ≫
        Fan.algebraicRealizationActionChartMap
          ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ := by
  apply pullback.hom_ext
  · simp
  · simp [affineToricChartMap_def]

end TauCeti.Toric.FanHom
end
