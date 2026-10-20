namespace P2MW.S_ModularCurve_FullLevel_eq_of_goodPt_of_reads_twoChartIntegralModel

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory.Limits

universe u

namespace E137

open AlgebraicCurve.TwoChartIntegralModel

set_option maxHeartbeats 1600000 in

theorem chartInf_spec {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V S : F → Prop) (y : ↥(XInf R F j))
    (hc : ∀ f : F, InStalkG j ((ιInf R F j).base y) f → V f ∧ (S f ↔ InMaxG j ((ιInf R F j).base y) f)) :
    ∀ b : ↥(chartAlgInf R F j), V (b : F) ∧ (S (b : F) ↔ b ∈ y.asIdeal) := by
  intro b
  have h1 : (1 : ↥(chartAlgInf R F j)) ∉ y.asIdeal := fun h => y.2.ne_top ((Ideal.eq_top_iff_one _).mpr h)

  have cross : ∀ y'' : ↥(XFin R F j), (ιFin R F j).base y'' = (ιInf R F j).base y →
      ∃ g h : ↥(chartAlgFin R F j), h ∉ y''.asIdeal ∧ (b : F) * (h : F) = (g : F) ∧
        (b ∈ y.asIdeal → g ∈ y''.asIdeal) := by
    intro y'' hy''
    obtain ⟨z, hz1, hz2⟩ := exists_of_ιInf_eq_ιFin j y y'' hy''.symm
    have hyz : y.asIdeal = Ideal.comap (inclInf R F j).toRingHom z.asIdeal := by
      rw [← hz1]; exact PrimeSpectrum.comap_asIdeal _ _
    have hy''z : y''.asIdeal = Ideal.comap (inclFin R F j).toRingHom z.asIdeal := by
      rw [← hz2]; exact PrimeSpectrum.comap_asIdeal _ _
    letI := (inclFin R F j).toRingHom.toAlgebra
    haveI := isLocalization_away_inclFin R F j
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hab⟩ :=
      IsLocalization.surj (Submonoid.powers (jChartFin R F j)) (inclInf R F j b)
    dsimp only at hab
    have hab' : (inclFin R F j) a = inclInf R F j b * (inclFin R F j) (jChartFin R F j ^ n) := hab.symm
    refine ⟨a, jChartFin R F j ^ n, ?_, ?_, ?_⟩
    · intro hmem
      have hu : IsUnit ((inclFin R F j) (jChartFin R F j ^ n)) := by
        rw [map_pow]; exact (isUnit_inclFin_jChartFin R F j).pow n
      rw [hy''z, Ideal.mem_comap] at hmem
      exact z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
    · have := congrArg Subtype.val hab'
      simp only [Subalgebra.coe_mul, coe_chartIncl, map_pow, SubmonoidClass.coe_pow] at this
      exact this.symm
    · intro hb
      rw [hy''z, Ideal.mem_comap]
      change (inclFin R F j) a ∈ z.asIdeal
      rw [hab']
      rw [hyz, Ideal.mem_comap] at hb
      exact Ideal.mul_mem_right _ _ hb
  have hst : InStalkG j ((ιInf R F j).base y) b := by
    refine ⟨fun y'' hy'' => ?_, fun y₂ hy₂ => ?_⟩
    · obtain ⟨g, h, hh, hbh, -⟩ := cross y'' hy''
      exact ⟨g, h, hh, hbh⟩
    · obtain rfl : y₂ = y := (ιInf R F j).isOpenEmbedding.injective hy₂
      exact ⟨b, 1, h1, by simp⟩
  obtain ⟨hV, hS⟩ := hc b hst
  refine ⟨hV, hS.trans ⟨fun hm => ?_, fun hb => ?_⟩⟩
  · obtain ⟨g, h, hh, hg, hbh⟩ := hm.2 y rfl
    have hbh' : b * h = g := Subtype.ext (by simpa using hbh)
    have : b * h ∈ y.asIdeal := hbh' ▸ hg
    exact ((y.2.mem_or_mem this).resolve_right hh)
  · refine ⟨fun y'' hy'' => ?_, fun y₂ hy₂ => ?_⟩
    · obtain ⟨g, h, hh, hbh, hg⟩ := cross y'' hy''
      exact ⟨g, h, hh, hg hb, hbh⟩
    · obtain rfl : y₂ = y := (ιInf R F j).isOpenEmbedding.injective hy₂
      exact ⟨b, 1, h1, hb, by simp⟩

end E137
end P2MW.S_ModularCurve_FullLevel_eq_of_goodPt_of_reads_twoChartIntegralModel
