public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative

namespace TauCeti.Toric.FanHom

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V}
  {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- The affine morphism from a source chart to the chart of the least target cone containing its
image. -/
noncomputable def affineToricChartMap (f : FanHom Φ Ψ) (σ : Φ.cones) :
    Φ.affineToricChart σ ⟶
      Ψ.affineToricChart ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩ :=
  affineToricSchemeMap (σ := σ.1) (τ := f.leastCone σ.2)
    Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
    -- Pin the source and target cone coercions at this polymorphic MapsTo argument.
    (show Set.MapsTo f.realMap (σ.1 : Set V) (f.leastCone σ.2 : Set V') from
      fun x hx ↦ f.map_le_leastCone σ.2 ⟨x, hx, rfl⟩)

end TauCeti.Toric.FanHom
end
