/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ValuationIntegers.AbsoluteValue
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# The absolute-value topology of a valuation of rank at most one

The metric on `WithAbs v.absoluteValue` is ultrametric. The canonical ring identity from
`WithVal v` to this normed copy is a uniform equivalence: its forward function sends
`WithVal.toVal v x` to `WithAbs.toAbs v.absoluteValue x`, and its inverse also preserves the
underlying element. No topology on the original division ring is chosen or assumed.

The rank-at-most-one data specify the real embedding used by the absolute value. Trivial
valuations are included; neither discreteness nor a numerical normalization is required.
In rank one on a valued field, Mathlib's `Valued.toNormedField` already supplies a normed-field
structure preserving the given uniformity. The comparison here concerns the two canonical
type synonyms, not an additional metric construction on the original field.

## References

* Mathlib's `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm` and
  `WithAbs.norm_eq_apply_ofAbs` supply the norm-to-ultrametric implication.
* Mathlib's `Valued.hasBasis_uniformity` and `Metric.uniformity_basis_dist` supply the
  valued and metric entourages. `Valuation.RankLeOne.exists_val_lt` includes the trivial
  restricted-value group, and `MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective` supplies
  each restricted-value radius over a division ring. The comparisons use
  `Valuation.absoluteValue_lt_iff`.
-/

@[expose] public section

universe u v

namespace Valuation

variable {K : Type u} [DivisionRing K] {Γ₀ : Type v}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.RankLeOne]

/-- The normed copy attached to the real absolute value of a rank-at-most-one valuation is
ultrametric, including when the valuation is trivial. -/
theorem isUltrametricDist_absoluteValue : IsUltrametricDist (WithAbs v.absoluteValue) := by
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  simpa only [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_add] using
    v.isNonarchimedean_absoluteValue x.ofAbs y.ofAbs

/-- The specified underlying ring identity is a uniform equivalence between the valued copy
and the normed absolute-value copy of a rank-at-most-one valued division ring. -/
noncomputable def absoluteValueUniformEquiv : WithVal v ≃ᵤ WithAbs v.absoluteValue where
  toEquiv := ((WithVal.equiv v).trans (WithAbs.equiv v.absoluteValue).symm).toEquiv
  uniformContinuous_toFun := by
    change UniformContinuous (fun x : WithVal v ↦ WithAbs.toAbs v.absoluteValue x.ofVal)
    apply ((Valued.hasBasis_uniformity (WithVal v) Γ₀).uniformContinuous_iff
      Metric.uniformity_basis_dist).mpr
    intro ε hε
    rcases RankLeOne.exists_val_lt v with htriv | hsmall
    · -- If the restricted unit group is trivial, the valuation ball of radius one is {0}.
      refine ⟨1, trivial, ?_⟩
      intro x y hxy
      have hxy' : v.restrict (y.ofVal - x.ofVal) < 1 :=
        v.restrict_lt_one_iff.mpr ((WithVal.valuation v).restrict_lt_one_iff.mp hxy)
      have hzero : y.ofVal - x.ofVal = 0 := by
        by_contra hne
        have hone : v.restrict (y.ofVal - x.ofVal) = 1 :=
          congrArg Units.val (htriv.elim (Units.mk0 _ (by
            simpa only [ne_eq, restrict_eq_zero_iff, map_eq_zero] using hne)) 1)
        exact (ne_of_lt hxy') hone
      simpa only [Set.mem_ofPred_eq, dist_eq_norm_sub', WithAbs.norm_eq_apply_ofAbs,
        WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs, hzero, map_zero] using hε
    · -- Otherwise rank-at-most-one coinitiality supplies a nonzero small radius.
      obtain ⟨a, ha, haε⟩ := hsmall (γ := ⟨ε, hε.le⟩)
        (NNReal.coe_ne_zero.mp hε.ne')
      have haε' : v.absoluteValue a < ε := by
        change (RankLeOne.hom' v (v.restrict a) : ℝ) < ε
        exact NNReal.coe_lt_coe.mpr haε
      refine ⟨Units.mk0 ((WithVal.valuation v).restrict (WithVal.toVal v a)) (by
        simpa only [ne_eq, restrict_eq_zero_iff, map_eq_zero, WithVal.toVal_eq_zero]
          using ha), trivial, ?_⟩
      intro x y hxy
      have hxy' : v (y.ofVal - x.ofVal) < v a :=
        (WithVal.valuation v).restrict_lt_iff.mp hxy
      have habs : v.absoluteValue (y.ofVal - x.ofVal) < ε :=
        ((v.absoluteValue_lt_iff _ _).mpr hxy').trans haε'
      simpa only [Set.mem_ofPred_eq, dist_eq_norm_sub', WithAbs.norm_eq_apply_ofAbs,
        WithAbs.ofAbs_sub, WithAbs.ofAbs_toAbs] using habs
  uniformContinuous_invFun := by
    change UniformContinuous (fun x : WithAbs v.absoluteValue ↦ WithVal.toVal v x.ofAbs)
    apply (Metric.uniformity_basis_dist.uniformContinuous_iff
      (Valued.hasBasis_uniformity (WithVal v) Γ₀)).mpr
    intro γ _
    -- Over a division ring every restricted-value radius is attained.
    obtain ⟨a, ha⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (WithVal.valuation v)) γ.1
    have ha' : (WithVal.valuation v).restrict a = γ.1 := ha
    have ha₀ : a.ofVal ≠ 0 := by
      intro h
      have hz : a = 0 := (WithVal.ofVal_eq_zero v a).mp h
      exact γ.ne_zero (ha'.symm.trans (by simp only [hz, map_zero]))
    refine ⟨v.absoluteValue a.ofVal, v.absoluteValue.pos ha₀, ?_⟩
    intro x y hxy
    have hxy' : v.absoluteValue (y.ofAbs - x.ofAbs) < v.absoluteValue a.ofVal := by
      simpa only [Set.mem_ofPred_eq, dist_eq_norm_sub', WithAbs.norm_eq_apply_ofAbs,
        WithAbs.ofAbs_sub] using hxy
    change (WithVal.valuation v).restrict
      (WithVal.toVal v (y.ofAbs - x.ofAbs)) < γ.1
    rw [← ha', restrict_lt_iff]
    exact (v.absoluteValue_lt_iff _ _).mp hxy'

/-- The uniform equivalence has exactly the canonical underlying ring equivalence. -/
theorem absoluteValueUniformEquiv_toEquiv :
    v.absoluteValueUniformEquiv.toEquiv =
      ((WithVal.equiv v).trans (WithAbs.equiv v.absoluteValue).symm).toEquiv := rfl

/-- The comparison preserves the underlying field or division-ring element. -/
@[simp]
theorem absoluteValueUniformEquiv_apply (x : WithVal v) :
    v.absoluteValueUniformEquiv x = WithAbs.toAbs v.absoluteValue x.ofVal := rfl

/-- The inverse comparison also preserves the underlying field or division-ring element. -/
@[simp]
theorem absoluteValueUniformEquiv_symm_apply (x : WithAbs v.absoluteValue) :
    v.absoluteValueUniformEquiv.symm x = WithVal.toVal v x.ofAbs := rfl

end Valuation
