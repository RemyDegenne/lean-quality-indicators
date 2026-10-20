public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree

attribute [local instance] ContMDiffMul.boundarylessManifold

variable [CompactSpace G]

theorem IsMaximalTorus.eq_lieSubalgebraOfSubgroup_of_isLieAbelian {T : Subgroup G}
    (hT : IsMaximalTorus T) {𝔞 : LieSubalgebra ℝ (LeftInvariantDerivation I G)} [IsLieAbelian 𝔞]
    (h𝔞 : lieSubalgebraOfSubgroup (I := I) T ≤ 𝔞) : 𝔞 = lieSubalgebraOfSubgroup (I := I) T :=
  le_antisymm
    (fun X hX => hT.mem_lieSubalgebraOfSubgroup_of_forall_lie_eq_zero fun Y hY => by
      have htriv := trivial_lie_zero 𝔞 𝔞 (⟨X, hX⟩ : 𝔞) ⟨Y, h𝔞 hY⟩
      simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using htriv)
    h𝔞

end TauCeti.Lie
end
end
