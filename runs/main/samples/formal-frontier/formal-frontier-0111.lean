@[expose] public section

open Filter

open scoped Topology Pointwise

universe u v

namespace ContinuousMonoidHom

variable {G : Type u} {K : Type v} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [Group K] [TopologicalSpace K]

@[to_additive]
theorem finite_quotient_kerLift [CompactSpace G] (f : G →ₜ* K)
    (V : Set K) (hV : V ∈ 𝓝 (1 : K))
    (hVsub : ∀ H : Subgroup K, (H : Set K) ⊆ V → H = ⊥) :
    Finite (G ⧸ f.toMonoidHom.ker) ∧
      DiscreteTopology (G ⧸ f.toMonoidHom.ker) ∧
      (QuotientGroup.kerLift f.toMonoidHom).comp
        (QuotientGroup.mk' f.toMonoidHom.ker) = f.toMonoidHom ∧
      ∀ lift : G ⧸ f.toMonoidHom.ker →* K,
        lift.comp (QuotientGroup.mk' f.toMonoidHom.ker) = f.toMonoidHom →
          lift = QuotientGroup.kerLift f.toMonoidHom := by
  have hopen := f.isOpen_ker_of_subgroup_free_nhds V hV hVsub
  have htriangle : (QuotientGroup.kerLift f.toMonoidHom).comp
      (QuotientGroup.mk' f.toMonoidHom.ker) = f.toMonoidHom := by
    ext x
    exact QuotientGroup.kerLift_mk f.toMonoidHom x
  refine ⟨Subgroup.quotient_finite_of_isOpen _ hopen,
    QuotientGroup.discreteTopology hopen, htriangle, ?_⟩
  intro lift hlift
  exact QuotientGroup.monoidHom_ext f.toMonoidHom.ker (hlift.trans htriangle.symm)

end ContinuousMonoidHom
end
