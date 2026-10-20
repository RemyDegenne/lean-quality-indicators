public noncomputable section

open IsLocalRing IsManifold

open scoped Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℂ E' H')
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

variable {I J}

namespace nodeLocalRing

variable (I J) (p : X) (q : Y)

variable {I J p q}

section Curve

section Snd

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] {p : X} {q : Y}
  {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hq : q ∈ e'.source)

theorem ker_fst_eq_span_sndCoordinate :
    RingHom.ker (fst 𝓘(ℂ) 𝓘(ℂ) p q) = Ideal.span {sndCoordinate (p := p) he' hq} := by
  refine le_antisymm (fun f hf ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).mpr (by simp))
  rw [RingHom.mem_ker] at hf
  -- The second branch germ vanishes at `q`, so it is a multiple of the coordinate there.
  have hq0 : holomorphicStructureSheaf.eval 𝓘(ℂ) Y q (snd 𝓘(ℂ) 𝓘(ℂ) p q f) = 0 := by
    rw [eval_snd, ← eval_fst, hf, map_zero]
  obtain ⟨g, hg⟩ :=
    (e'.holomorphicCoordinateGerm_dvd_iff_eval_eq_zero he' q hq _).mpr hq0
  obtain ⟨g', rfl⟩ : ∃ g', snd 𝓘(ℂ) 𝓘(ℂ) p q g' = g := snd_surjective g
  refine Ideal.mem_span_singleton'.mpr ⟨g', ext ?_ ?_⟩
  · rw [map_mul, fst_sndCoordinate, mul_zero, hf]
  · rw [map_mul, snd_sndCoordinate, hg, mul_comm]

end Snd
end Curve
end nodeLocalRing
end TauCeti.holomorphicStructureSheaf
end
