public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

set_option linter.unusedSectionVars false

section CharTwoGeom

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem polarNondegOn_fixSub_orthEight (hQ : (polarBilin Q).Nondegenerate) {E : Subgroup (V ≃ₗ[K] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (Nat.card E)) :
    PolarNondegOn Q (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub E) := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  haveI := Fintype.ofFinite E
  intro x hx hxx
  apply eq_zero_of_polar_eq_zero hQ
  intro v
  have haF : (∑ g : E, (g : V ≃ₗ[K] V) v) ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fixSub E := by
    intro h hh
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : E)) _ _ fun g => rfl
  have h1 : polar Q x (∑ g : E, (g : V ≃ₗ[K] V) v) = polar Q x v := by
    rw [← polarBilin_apply_apply, map_sum]
    have : ∀ g : E, polarBilin Q x ((g : V ≃ₗ[K] V) v) = polarBilin Q x v := fun g => by
      rw [polarBilin_apply_apply, polarBilin_apply_apply]
      conv_lhs => rw [← hx g g.2]
      exact polar_map_of_mem (hEO g.2) x v
    simp only [this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K, natCast_eq_one_of_odd_orthEight hodd,
      one_smul, polarBilin_apply_apply]
  rw [← h1]
  exact hxx _ haF

end CharTwoGeom
end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz10
end
