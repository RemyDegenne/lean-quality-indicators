public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

namespace ContinuousGroupCohomology

universe uR uG uA

variable {R : Type uR} [CommRing R]

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

namespace LevelCompact

local instance relativeNormSubgroup_finiteIndex (U V : OpenSubgroup G) :
    (relativeNormSubgroup U V).toSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

local instance relativeNormTransversalFintype (U V : OpenSubgroup G)
    (T : (relativeNormSubgroup U V).toSubgroup.RightTransversal) :
    Fintype ↥(T : Set U) :=
  T.2.finite_right.fintype

open ContinuousCohomology.CorestrictionTransversal

@[simp]
theorem relativeNorm_refl (A : Rep.{uA} R G) (U : OpenSubgroup G) :
    relativeNorm A U U le_rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  let T : (relativeNormSubgroup U U).toSubgroup.RightTransversal := default
  rw [relativeNorm_eq_withTransversal A U U le_rfl T]
  rw [relativeNormWithTransversal_coe]
  have hterm (t : ↥(T : Set U)) :
      A.ρ (((t : U) : G)⁻¹) x = x := by
    exact x.2 ⟨((t : U)⁻¹), U.inv_mem (t : U).2⟩
  simp_rw [hterm]
  have htop : (relativeNormSubgroup U U).toSubgroup = ⊤ := by
    apply le_antisymm
    · exact le_top
    · intro y _
      exact y.2
  let _ : (relativeNormSubgroup U U).toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let _ : Fintype ↥(T : Set U) := T.2.finite_right.fintype
  let _ : Fintype (_root_.Quotient
      (QuotientGroup.rightRel (relativeNormSubgroup U U).toSubgroup)) :=
    Fintype.ofEquiv _ T.2.rightQuotientEquiv.symm
  let _ : Subsingleton (_root_.Quotient
      (QuotientGroup.rightRel (relativeNormSubgroup U U).toSubgroup)) :=
    ⟨by
      intro a b
      induction a using Quotient.inductionOn with
      | _ a =>
        induction b using Quotient.inductionOn with
        | _ b =>
          apply Quotient.sound
          apply QuotientGroup.rightRel_apply.mpr
          rw [htop]
          trivial⟩
  let _ : Unique (_root_.Quotient
      (QuotientGroup.rightRel (relativeNormSubgroup U U).toSubgroup)) :=
    { default := Quotient.mk'' (1 : U)
      uniq := fun _ => Subsingleton.elim _ _ }
  have hcard : Fintype.card ↥(T : Set U) = 1 := by
    rw [← Fintype.card_congr T.2.rightQuotientEquiv]
    exact Fintype.card_unique
  rw [Finset.sum_const, Finset.card_univ, hcard, one_nsmul]
  rfl

end LevelCompact
end ContinuousGroupCohomology
end
end
