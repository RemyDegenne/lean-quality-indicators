universe v

open scoped DirectSum HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

variable (K) in
/-- The principal classes of a fixed Hahn degree form the `K`-subspace `P_α` from LM24,
Proposition 5.2.4 and Corollary 5.2.5. -/
def principalDegreeClasses (α : NatOrdinal) :
    Submodule K
      ((HahnSeries.Nonpositive.degreeValuation K).Component α) where
  carrier := {x | IsPrincipalDegreeClass α x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    change IsPrincipalDegreeClass α x at hx
    change IsPrincipalDegreeClass α y at hy
    change IsPrincipalDegreeClass α (x + y)
    rw [isPrincipalDegreeClass_iff] at hx hy ⊢
    rcases hx with rfl | ⟨p, hp, hpDegree, rfl⟩
    · simpa using hy
    rcases hy with rfl | ⟨q, hq, hqDegree, rfl⟩
    · exact Or.inr ⟨p, hp, hpDegree, by simp⟩
    have hsumLE : (((p + q : Series K) : K⟦ℝ⟧)).degree ≤
        (α : WithBot NatOrdinal) :=
      (HahnSeries.degree_add_le (p : K⟦ℝ⟧) (q : K⟦ℝ⟧)).trans
        (max_le hpDegree.le hqDegree.le)
    have hprojection :
        degreeLayerMk α p hpDegree.le +
            degreeLayerMk α q hqDegree.le =
          degreeLayerMk α (p + q) hsumLE :=
      (degreeLayerMk_add α p q hpDegree.le hqDegree.le).symm
    by_cases hzero : degreeLayerMk α (p + q) hsumLE = 0
    · exact Or.inl (hprojection.trans hzero)
    · have hsumNotLt : ¬(((p + q : Series K) : K⟦ℝ⟧).degree <
          (α : WithBot NatOrdinal)) := by
        intro hlt
        apply hzero
        let w := HahnSeries.Nonpositive.degreeValuation K
        change w.componentMk α ⟨p + q, _⟩ = 0
        rw [w.componentMk_eq_zero_iff,
          HahnSeries.Nonpositive.degreeValuation_apply]
        exact hlt
      have hsumDegree : (((p + q : Series K) : K⟦ℝ⟧)).degree =
          (α : WithBot NatOrdinal) :=
        le_antisymm hsumLE (le_of_not_gt hsumNotLt)
      have hsumPrincipal : HahnSeries.Nonpositive.IsPrincipal (p + q) :=
        hp.add_of_degree_eq hq
          (hqDegree.trans hpDegree.symm)
          (hsumDegree.trans hpDegree.symm)
      exact Or.inr ⟨p + q, hsumPrincipal, hsumDegree, hprojection⟩
  smul_mem' := by
    intro k x hx
    change IsPrincipalDegreeClass α x at hx
    change IsPrincipalDegreeClass α (k • x)
    rw [isPrincipalDegreeClass_iff] at hx ⊢
    rcases hx with rfl | ⟨p, hp, hpDegree, rfl⟩
    · exact Or.inl (smul_zero k)
    · by_cases hk : k = 0
      · subst k
        exact Or.inl
          (zero_smul K (degreeLayerMk α p hpDegree.le))
      · have hkpDegree :
            ((((HahnSeries.Nonpositive.C : K →+* Series K) k) * p : Series K) :
                K⟦ℝ⟧).degree = (α : WithBot NatOrdinal) := by
          rw [← ordinalValueDegree_eq_degree_of_isPrincipal (hp.const_mul hk),
            ordinalValueDegree_C_mul hk, ordinalValueDegree_eq_degree_of_isPrincipal hp, hpDegree]
        exact Or.inr
          ⟨(HahnSeries.Nonpositive.C : K →+* Series K) k * p,
            hp.const_mul hk, hkpDegree,
            smul_degreeLayerMk α k p hpDegree.le⟩

end Berarducci
end
