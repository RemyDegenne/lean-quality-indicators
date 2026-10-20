public section

open AlgebraicGeometry CategoryTheory Limits Multiplicative

namespace TauCeti.Toric.FanHom

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V'] {i : N →+ V}
  {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

section

variable {N'' : Type u} {V'' : Type*} [AddCommGroup N''] [AddCommGroup V''] [Module ℝ V'']
  {i'' : N'' →+ V''} {Ω : Fan i''}

@[simp]
theorem algebraicMap_comp (g : FanHom Ψ Ω) (f : FanHom Φ Ψ) :
    (g.comp f).algebraicMap = f.algebraicMap ≫ g.algebraicMap := by
  apply Fan.algebraicRealization_hom_ext Φ
  intro σ
  let τ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  let υ : Ω.cones := ⟨g.leastCone τ.2, g.leastCone_mem τ.2⟩
  let κ : Ω.cones := ⟨(g.comp f).leastCone σ.2, (g.comp f).leastCone_mem σ.2⟩
  have hκ_le_υ : κ.1 ≤ υ.1 := by
    apply (g.comp f).leastCone_le σ.2 (g.leastCone_mem τ.2)
    rw [FanHom.comp_realMap, ← PointedCone.map_map]
    exact (Submodule.map_mono (f.map_le_leastCone σ.2)).trans (g.map_le_leastCone τ.2)
  have hκυ : κ.1.IsFaceOf υ.1 := Ω.isFaceOf_of_le υ.2 κ.2 hκ_le_υ
  have hchart :
      (g.comp f).affineToricChartMap σ ≫ faceAffineToricSchemeMap Ω.lattice hκυ =
        f.affineToricChartMap σ ≫ g.affineToricChartMap τ := by
    rw [affineToricChartMap_def, affineToricChartMap_def, affineToricChartMap_def,
      faceAffineToricSchemeMap_eq_affineToricSchemeMap]
    rw [affineToricSchemeMap_comp, affineToricSchemeMap_comp]
    simp [FanHom.comp_latticeMap, FanHom.comp_realMap]
  rw [affineToricChartι_comp_algebraicMap]
  rw [affineToricChartι_comp_algebraicMap_assoc]
  rw [affineToricChartι_comp_algebraicMap]
  rw [← Fan.faceAffineToricSchemeMap_comp_affineToricChartι hκυ]
  rw [← Category.assoc, hchart]
  simp only [τ, υ, Category.assoc]

end
end TauCeti.Toric.FanHom
end
