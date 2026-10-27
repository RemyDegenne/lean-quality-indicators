public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {c : Γ.Coloring (Fin 2)} {q : ℕ}

theorem existsUnique_mem_spanSet_of_mem_clSet (hΓ : IsThasQuadrangle Γ c q)
    {y z x : V} (hy : c y = 0) (hyz : Γ.dist y z = 4) (hx : c x = 0)
    (hxT : x ∉ traceSet Γ y z)
    {u : V} (hu : u ∈ spanSet Γ y z) (hxu : Γ.dist x u ≤ 2) :
    ∃! u' : V, u' ∈ spanSet Γ y z ∧ Γ.dist x u' ≤ 2 := by
  classical
  have hP : IsGeneralizedPolygon Γ 4 := hΓ.gp
  have hT : IsThick Γ := hΓ.thick
  refine ⟨u, ⟨hu, hxu⟩, ?_⟩
  rintro u' ⟨hu', hxu'⟩
  by_contra hne
  have hne' : u ≠ u' := Ne.symm hne
  have hu4 : Γ.dist u u' = 4 :=
    dist_eq_four_of_mem_span hP hT hyz hu hu' hne'
  have hu0 : c u = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu
  have hu'0 : c u' = 0 := color_eq_zero_of_mem_span hP hT hy hyz hu'
  have hxmem : x ∈ traceSet Γ u u' :=
    mem_traceSet_of_dist_le_two hP hu0 hu4 hx hxu hxu'
  have htrace : traceSet Γ u u' = traceSet Γ y z :=
    (span_eq_of_mem hP hT hyz hu hu' hne').2.2
  exact hxT (htrace ▸ hxmem)

end CFSG.Geometry.GeneralizedQuadrangles
end
