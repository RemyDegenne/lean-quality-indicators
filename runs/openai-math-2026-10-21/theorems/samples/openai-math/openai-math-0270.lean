namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory

open scoped Topology ContDiff

namespace RVM.Magnetic

section

attribute [local instance] Measure.Subtype.measureSpace

local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

lemma physical_transport_annulus_log_bound (P H A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (U t N ε R : ℝ) (f : Particle),
      0<t → t≤U → U≤H → 0≤N → 0<ε → R≤t →
      ContinuousOn f {p | p.1∈Icc (0:ℝ) U} →
      (∀ s∈Icc (0:ℝ) U, ∀ v, Differentiable ℝ (fun y => f (s,y,v))) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => f (s,z,v)) y‖≤N) →
      ∀ x, |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P f t x e i z|≤
        1+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨K,hK,hkb⟩ := transportSpatialDivergence_uniform_bound P e i
  let C := volume.real (closedBall (0:Vec) P)*(4*Real.pi)*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,C*A,hC,mul_nonneg hC hA,?_⟩
  intro U t N ε R f ht htU hUH hN hε hRt hfc hfd hfA hfN x
  have htt : t∈Icc (0:ℝ) U := ⟨ht.le,htU⟩
  have hh := singular_radial_log_bound_norm ht (htU.trans hUH) (mul_nonneg hC hA) (mul_nonneg hC hN)
    (transportSingularShell_continuousOn x e i hfc htt)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).1)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).2)
  rw [transportSingularBulk_annulus x e i hε hRt htU hfc]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply le_trans _ hh.2
  exact integral_mono_measure (Measure.restrict_mono_set volume (by
    intro r hr
    exact ⟨hε.trans_le hr.1,hr.2.le.trans hRt⟩))
    (Filter.Eventually.of_forall (fun r => norm_nonneg _)) hh.1.norm

end
end RVM.Magnetic
end
end
end OAI
