public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

universe u v

section Rigidity

variable {V : Type u} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {H : Type v} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

theorem eq_one_of_mem_rootGroup_of_fix_opposite_end (hP : IsGeneralizedPolygon Γ 4)
    (hT : IsThick Γ) (p : GPath Γ 4) (hp : p.NoBack)
    {g : H} (hg : g ∈ rootGroup H Γ (p 1) (p 2) (p 3)) {w : V}
    (hw : Γ.dist (p 1) w = 4) (hgw : g • w = w) : g = 1 := by
  classical
  have hw0 : Γ.dist w (p 0) = 3 := by
    have hadj : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
    have h41 : Γ.dist w (p 1) = 4 := by rw [SimpleGraph.dist_comm]; exact hw
    rcases hP.dist_adj hadj w with h | h
    · omega
    · have := hP.dist_le (by norm_num) w (p 0)
      omega
  let c := proj hP hw0
  have hc_adj : Γ.Adj (p 0) c := proj_adj hP hw0
  have hc_dist : Γ.dist w c = 2 := proj_dist hP hw0
  have hc_ne : c ≠ p 1 := by
    intro h
    rw [h, SimpleGraph.dist_comm, hw] at hc_dist
    omega
  have hg1 : g ∈ fixingSubgroup H (Γ.neighborSet (p 1)) := ((mem_rootGroup H).mp hg).1
  have hg2 : g ∈ fixingSubgroup H (Γ.neighborSet (p 2)) := ((mem_rootGroup H).mp hg).2.1
  have hg3 : g ∈ fixingSubgroup H (Γ.neighborSet (p 3)) := ((mem_rootGroup H).mp hg).2.2
  have hgp0 : g • p 0 = p 0 :=
    (mem_fixingSubgroup_iff H).mp hg1 (p 0) (by simpa using (p.adj 0 (by omega)).symm)
  have hgc : g • c = c := by
    have h1 : Γ.Adj (p 0) (g • c) := by
      have h' := (GraphAction.adj_smul g (p 0) c).mpr hc_adj
      rwa [hgp0] at h'
    have h2 : Γ.dist w (g • c) = 2 := by
      rw [← hgw, GPath.dist_smul hP.connected g w c]
      exact hc_dist
    have h' := eq_proj hP hw0 h1 h2
    simpa [c] using h'
  let q : GPath Γ 4 := p.rev
  have hq3 : q 3 = p 1 := by simp [q]
  have hq4 : q 4 = p 0 := by simp [q]
  have hq : q.NoBack := hp.rev
  have hfix : ∀ i, 1 ≤ i → i ≤ 3 → ∀ v, Γ.Adj (q i) v → g • v = v := by
    intro i hi1 hi3 v hv
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact (mem_fixingSubgroup_iff H).mp hg3 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hg2 v (by simpa [q] using hv)
    · exact (mem_fixingSubgroup_iff H).mp hg1 v (by simpa [q] using hv)
  have hpg : IsGenPolygon Γ 4 := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hTh : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hall : ∀ v : V, g • v = v :=
    hpg.smul_eq_of_fix_root (by omega) hTh q hq hfix (by simpa [hq4] using hc_adj)
      (by simpa [hq3] using hc_ne) hgc
  refine eq_of_smul_eq_smul (m₁ := g) (m₂ := 1) (fun v : V => ?_)
  rw [one_smul]
  exact hall v

end Rigidity
end CFSG.Geometry.GeneralizedQuadrangles
end
