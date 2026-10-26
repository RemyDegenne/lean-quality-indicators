/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan
public import AlgebraicGroups.Algebra.Coalgebra.MonoidAlgebra
public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Hom
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Coalgebra coordinates on the span of group-like elements

Over a field, the span of the group-like elements is a subcoalgebra. Canonical
evaluation identifies it, as a coalgebra, with the free diagonal coalgebra indexed
by those group-like elements. The inverse coefficients are the stock linear
coordinates of the linearly independent group-like family. In these coordinates,
ambient comultiplication is diagonal and the counit is the sum of coefficients.

The equivalence is with the span, not necessarily the whole ambient coalgebra.
No finite-dimensionality or nonempty group-like family is required.

## References

Mathlib supplies `linearIndep_groupLikeVal`,
`LinearIndependent.linearCombinationEquiv`, `LinearIndependent.repr` and
`MonoidAlgebra.coeffLinearEquiv`. The subcoalgebra assembles the span-closure
result in `AlgebraicGroups.Algebra.Coalgebra.GroupLikeSpan` with the constructor,
restricted coalgebra and codomain restriction in the subcoalgebra modules.
The equivalence uses Mathlib's `CoalgEquiv.ofBijective` on canonical evaluation.
-/

@[expose] public section

universe uK uC

open scoped MonoidAlgebra TensorProduct

variable {K : Type uK} {C : Type uC}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

namespace Subcoalgebra

variable (K C) in
/-- The subcoalgebra spanned by all group-like elements of a coalgebra over a field. -/
def groupLikeSpan : Subcoalgebra K C :=
  Subcoalgebra.mk' (Submodule.span K (Set.range (GroupLike.val (R := K) (A := C))))
    (fun {x} => Coalgebra.comul_mem_range_mapIncl_span_of_isGroupLikeElem
      (R := K) (C := C) (s := Set.range (GroupLike.val (R := K) (A := C)))
      (x := x) (by
        rintro _ ⟨g, rfl⟩
        exact g.isGroupLikeElem_val))

/-- The underlying subspace of the group-like subcoalgebra is the canonical linear span. -/
@[simp]
theorem groupLikeSpan_toSubmodule :
    (groupLikeSpan K C).toSubmodule =
      Submodule.span K (Set.range (GroupLike.val (R := K) (A := C))) :=
  rfl

/-- Membership in the group-like subcoalgebra is membership in the linear span. -/
@[simp]
theorem mem_groupLikeSpan_iff {x : C} :
    x ∈ groupLikeSpan K C ↔
      x ∈ Submodule.span K (Set.range (GroupLike.val (R := K) (A := C))) := by
  rw [← mem_toSubmodule, groupLikeSpan_toSubmodule]

/-- Every group-like element belongs to the group-like subcoalgebra. -/
theorem groupLike_mem_groupLikeSpan (g : GroupLike K C) :
    g.val ∈ groupLikeSpan K C := by
  exact mem_groupLikeSpan_iff.mpr (Submodule.subset_span ⟨g, rfl⟩)

/-- The group-like subcoalgebra is the least subcoalgebra containing every group-like element. -/
theorem groupLikeSpan_le_iff (D : Subcoalgebra K C) :
    (groupLikeSpan K C).toSubmodule ≤ D.toSubmodule ↔
      ∀ g : GroupLike K C, g.val ∈ D := by
  rw [groupLikeSpan_toSubmodule, Submodule.span_le]
  constructor
  · intro h g
    exact h ⟨g, rfl⟩
  · rintro h _ ⟨g, rfl⟩
    exact h g

/-- With no group-like elements, the group-like subcoalgebra has zero underlying subspace. -/
theorem groupLikeSpan_eq_bot_of_isEmpty [IsEmpty (GroupLike K C)] :
    (groupLikeSpan K C).toSubmodule = ⊥ := by
  rw [groupLikeSpan_toSubmodule, Set.range_eq_empty, Submodule.span_empty]

end Subcoalgebra

namespace GroupLike

/-- Canonical evaluation is a coalgebra equivalence from the free diagonal coalgebra
onto the group-like span, with its existing restricted coalgebra structure. -/
noncomputable def spanCoalgebraEquiv :
    K[GroupLike K C] ≃ₗc[K] Subcoalgebra.groupLikeSpan K C :=
  CoalgEquiv.ofBijective
    (f := (MonoidAlgebra.liftGroupLikeCoalgHom
      (id : GroupLike K C → GroupLike K C)).codRestrict
        (Subcoalgebra.groupLikeSpan K C) (by
          intro x
          apply Subcoalgebra.mem_groupLikeSpan_iff.mpr
          have hx := LinearMap.mem_range_self
            (MonoidAlgebra.liftGroupLikeCoalgHom
              (id : GroupLike K C → GroupLike K C)).toLinearMap x
          rw [MonoidAlgebra.range_liftGroupLikeCoalgHom] at hx
          simpa only [id_eq, CoalgHom.toLinearMap_eq_coe,
            CoalgHom.coe_toLinearMap] using hx))
    (by
      constructor
      · intro x y h
        apply (MonoidAlgebra.coeffLinearEquiv K).injective
        apply linearIndep_groupLikeVal (R := K) (A := C)
        have h' :
            (MonoidAlgebra.liftGroupLikeCoalgHom
              (id : GroupLike K C → GroupLike K C)).toLinearMap x =
            (MonoidAlgebra.liftGroupLikeCoalgHom
              (id : GroupLike K C → GroupLike K C)).toLinearMap y := by
          simpa only [CoalgHom.coe_codRestrict, CoalgHom.toLinearMap_eq_coe,
            CoalgHom.coe_toLinearMap] using
            congrArg (fun z : Subcoalgebra.groupLikeSpan K C => (z : C)) h
        simpa only [MonoidAlgebra.liftGroupLikeCoalgHom_toLinearMap,
          LinearMap.comp_apply, LinearEquiv.coe_coe, id_eq] using h'
      · intro x
        refine ⟨(MonoidAlgebra.coeffLinearEquiv K).symm
          ((linearIndep_groupLikeVal (R := K) (A := C)).repr x), ?_⟩
        apply Subcoalgebra.coe_injective
        simpa only [CoalgHom.coe_codRestrict] using
          (calc
            MonoidAlgebra.liftGroupLikeCoalgHom (id : GroupLike K C → GroupLike K C)
                ((MonoidAlgebra.coeffLinearEquiv K).symm
                  ((linearIndep_groupLikeVal (R := K) (A := C)).repr x)) =
                Finsupp.linearCombination K (val : GroupLike K C → C)
                  ((linearIndep_groupLikeVal (R := K) (A := C)).repr x) := by
              simpa only [CoalgHom.toLinearMap_eq_coe, CoalgHom.coe_toLinearMap,
                LinearMap.comp_apply, LinearEquiv.coe_coe, id_eq,
                LinearEquiv.apply_symm_apply] using
                (LinearMap.congr_fun (MonoidAlgebra.liftGroupLikeCoalgHom_toLinearMap
                  (id : GroupLike K C → GroupLike K C))
                  ((MonoidAlgebra.coeffLinearEquiv K).symm
                    ((linearIndep_groupLikeVal (R := K) (A := C)).repr x)))
            _ = (x : C) :=
              (linearIndep_groupLikeVal (R := K) (A := C)).linearCombination_repr x))

/-- Inclusion after the equivalence is coalgebra evaluation on the identity family. -/
@[simp]
theorem subtype_comp_spanCoalgebraEquiv :
    (Subcoalgebra.groupLikeSpan K C).subtype.comp
        (spanCoalgebraEquiv (K := K) (C := C)).toCoalgHom =
      MonoidAlgebra.liftGroupLikeCoalgHom
        (id : GroupLike K C → GroupLike K C) := by
  exact CoalgHom.subtype_comp_codRestrict (K := K) (C := C)
    (A := K[GroupLike K C])
    (MonoidAlgebra.liftGroupLikeCoalgHom
      (id : GroupLike K C → GroupLike K C))
    (Subcoalgebra.groupLikeSpan K C) _

/-- The ambient value of the equivalence is evaluation of the same coefficients. -/
@[simp]
theorem spanCoalgebraEquiv_apply_coe (x : K[GroupLike K C]) :
    (spanCoalgebraEquiv x : C) = MonoidAlgebra.liftGroupLikeCoalgHom
      (id : GroupLike K C → GroupLike K C) x := by
  exact CoalgHom.congr_fun (subtype_comp_spanCoalgebraEquiv (K := K) (C := C)) x

/-- The underlying linear equivalence is the canonical stock linear-combination equivalence. -/
theorem spanCoalgebraEquiv_toLinearEquiv :
    (spanCoalgebraEquiv (K := K) (C := C)).toLinearEquiv =
      (MonoidAlgebra.coeffLinearEquiv K).trans
        (linearIndep_groupLikeVal (R := K) (A := C)).linearCombinationEquiv := by
  apply LinearEquiv.ext
  intro x
  apply Subcoalgebra.coe_injective
  calc
    ((spanCoalgebraEquiv (K := K) (C := C)).toLinearEquiv x : C) =
        (spanCoalgebraEquiv x : C) :=
      congrArg (fun z : Subcoalgebra.groupLikeSpan K C => (z : C))
        (congrFun (CoalgEquiv.coe_toLinearEquiv
          (spanCoalgebraEquiv (K := K) (C := C))) x)
    _ = MonoidAlgebra.liftGroupLikeCoalgHom
        (id : GroupLike K C → GroupLike K C) x := spanCoalgebraEquiv_apply_coe x
    _ = Finsupp.linearCombination K (GroupLike.val (R := K) (A := C))
        ((MonoidAlgebra.coeffLinearEquiv K) x) :=
      LinearMap.congr_fun (MonoidAlgebra.liftGroupLikeCoalgHom_toLinearMap
        (id : GroupLike K C → GroupLike K C)) x
    _ = _ :=
      (LinearIndependent.linearCombinationEquiv_apply_coe
        (linearIndep_groupLikeVal (R := K) (A := C))
        ((MonoidAlgebra.coeffLinearEquiv K) x)).symm

/-- The equivalence sends a monomial to the corresponding multiple of its group-like element. -/
@[simp]
theorem spanCoalgebraEquiv_single (g : GroupLike K C) (r : K) :
    spanCoalgebraEquiv (MonoidAlgebra.single g r) =
      r • (⟨g.val, Subcoalgebra.groupLike_mem_groupLikeSpan g⟩ :
        Subcoalgebra.groupLikeSpan K C) := by
  apply Subcoalgebra.coe_injective
  simp only [spanCoalgebraEquiv_apply_coe, MonoidAlgebra.liftGroupLikeCoalgHom_single,
    id_eq, Subcoalgebra.coe_smul]

/-- Inverse coefficients are exactly the stock coordinates of the independent group-like family. -/
theorem spanCoalgebraEquiv_symm_coeff (x : Subcoalgebra.groupLikeSpan K C) :
    ((spanCoalgebraEquiv (K := K) (C := C)).symm x).coeff =
      (linearIndep_groupLikeVal (R := K) (A := C)).repr x := by
  have h := congrArg
    (fun e : K[GroupLike K C] ≃ₗ[K] Subcoalgebra.groupLikeSpan K C => e.symm x)
    (spanCoalgebraEquiv_toLinearEquiv (K := K) (C := C))
  exact congrArg (fun y : K[GroupLike K C] => y.coeff) h

/-- A group-like generator has singleton inverse coordinates. -/
@[simp]
theorem spanCoalgebraEquiv_symm_groupLike (g : GroupLike K C) :
    (spanCoalgebraEquiv (K := K) (C := C)).symm
        ⟨g.val, Subcoalgebra.groupLike_mem_groupLikeSpan g⟩ =
      MonoidAlgebra.single g 1 := by
  apply EquivLike.injective (spanCoalgebraEquiv (K := K) (C := C))
  simp only [CoalgEquiv.apply_symm_apply, spanCoalgebraEquiv_single, one_smul]

/-- Ambient comultiplication is diagonal in the inverse coalgebra coordinates. -/
theorem comul_eq_sum_spanCoefficients (x : Subcoalgebra.groupLikeSpan K C) :
    Coalgebra.comul (R := K) (x : C) =
      ((spanCoalgebraEquiv (K := K) (C := C)).symm x).coeff.sum
        (fun g r => r • (g.val ⊗ₜ[K] g.val)) := by
  let f := MonoidAlgebra.liftGroupLikeCoalgHom
    (id : GroupLike K C → GroupLike K C)
  let y := (spanCoalgebraEquiv (K := K) (C := C)).symm x
  calc
    Coalgebra.comul (R := K) (x : C) = Coalgebra.comul (R := K) (f y) := by
      rw [← spanCoalgebraEquiv_apply_coe, CoalgEquiv.apply_symm_apply]
    _ = TensorProduct.map f.toLinearMap f.toLinearMap
        (Coalgebra.comul (R := K) y) :=
      (CoalgHomClass.map_comp_comul_apply f y).symm
    _ = _ := by
      rw [MonoidAlgebra.comul_eq_sum_coeff, map_finsuppSum]
      simp only [map_smul, TensorProduct.map_tmul, f, y, CoalgHom.toLinearMap_eq_coe,
        CoalgHom.coe_toLinearMap, MonoidAlgebra.liftGroupLikeCoalgHom_single, id_eq, one_smul]

/-- The ambient counit is the sum of the inverse coalgebra coordinates. -/
theorem counit_eq_sum_spanCoefficients (x : Subcoalgebra.groupLikeSpan K C) :
    Coalgebra.counit (R := K) (x : C) =
      ((spanCoalgebraEquiv (K := K) (C := C)).symm x).coeff.sum (fun _ r => r) := by
  let f := MonoidAlgebra.liftGroupLikeCoalgHom
    (id : GroupLike K C → GroupLike K C)
  let y := (spanCoalgebraEquiv (K := K) (C := C)).symm x
  calc
    Coalgebra.counit (R := K) (x : C) = Coalgebra.counit (R := K) (f y) := by
      rw [← spanCoalgebraEquiv_apply_coe, CoalgEquiv.apply_symm_apply]
    _ = Coalgebra.counit (R := K) y := CoalgHomClass.counit_comp_apply f y
    _ = _ := MonoidAlgebra.counit_eq_sum_coeff y

end GroupLike
