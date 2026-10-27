public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

open CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement

open CFSG.ComponentClassification.CatalogueBCentralQuotient (derivedPreimage
  derivedPreimage_eq_commutator derivedPreimage_map derivedPreimage_perfect)

section Central

theorem glaPComponent_derivedPreimage {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {A : Subgroup G} (g : ↥A →* X) (hg : g.ker ≤ Subgroup.center ↥A)
    {M J : Subgroup X} (hgM : g.range ≤ M) (hJ : GLAPComponent p M J) (hJg : J ≤ g.range) :
    GLAPComponent p A ((derivedPreimage g J).map A.subtype) ∧ (derivedPreimage g J).map g = J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set f : ↥A →* ↥g.range := g.rangeRestrict with hfdef
  have hf : Function.Surjective f := g.rangeRestrict_surjective
  have hfker : f.ker ≤ Subgroup.center ↥A := by
    rw [hfdef, MonoidHom.ker_rangeRestrict]
    exact hg
  have hJ₁ : GLAPComponent p g.range J := glaPComponent_of_le hp hJ hJg hgM
  obtain ⟨-, hJP⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ₁
  have hL := CFSG.ComponentClassification.CatalogueBCentralQuotient.pComponent_derivedPreimage p
    f hf hfker (J.subgroupOf g.range) hJP
  have hcomap : (J.subgroupOf g.range).comap f = J.comap g := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  have heq : derivedPreimage f (J.subgroupOf g.range) = derivedPreimage g J := by
    rw [derivedPreimage_eq_commutator, derivedPreimage_eq_commutator, hcomap]
  have hmap := CFSG.ComponentClassification.CatalogueBCentralQuotient.pComponent_right_inverse p
    f hf (J.subgroupOf g.range) hJP
  rw [heq] at hL hmap
  refine ⟨(CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).2
    ⟨Subgroup.map_subtype_le _, ?_⟩, ?_⟩
  · have h1 : ((derivedPreimage g J).map A.subtype).subgroupOf A = derivedPreimage g J :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
    rw [h1]
    exact hL
  · have h2 := congrArg (Subgroup.map g.range.subtype) hmap
    rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJg] at h2
    exact h2

end Central
end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen
end
