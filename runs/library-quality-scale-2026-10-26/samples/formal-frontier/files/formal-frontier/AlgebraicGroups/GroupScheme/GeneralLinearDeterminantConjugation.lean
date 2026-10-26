/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.SplitKernelSemidirect
public import AlgebraicGroups.GroupScheme.GeneralLinearDeterminantProduct

/-!
# Diagonal conjugation on the determinant-one group scheme

The diagonal section of the determinant restricts conjugation to the actual
special-linear kernel. Its affine points agree with conjugation of native
special-linear matrices over every commutative coefficient algebra.

The section-first product carries the twisted law
`F(s,t) * F(s',t') = F(alpha(t'⁻¹,s) * s',t*t')`, not direct-product
multiplication; the restricted action itself is defined on the genuine
kernel pullback, rather than reconstructed from selected points.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, XIII §3, item 3.14
  (field-base determinant splitting with the diagonal factor on the right).
  The left-factor conjugation and scheme-level twisted law
  below use the different section-first convention.
* `AlgebraicGroups.GroupObject.SplitKernelSemidirect` and
  `SplitKernelProduct` give the general kernel action and twisted product.
  Mathlib's `CategoryTheory/Monoidal/Cartesian/Grp.lean` supplies the
  group-object conjugation; `Data/Matrix/Mul.lean` gives the diagonal entry
  identities used with the local section and native matrix SL APIs.
-/

public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The actual morphism over `Spec K` restricting conjugation by the determinant
section to its categorical determinant-one kernel. -/
def generalLinearDeterminantConj (pivot : n) :
    multiplicativeGroupUnderlyingScheme K ⊗ specialLinearGroupUnderlyingScheme K n ⟶
      specialLinearGroupUnderlyingScheme K n :=
  splitKernelConj (specialLinearInclusion K n).hom.hom
    (generalLinearDeterminantSchemeHom K n).hom.hom
    (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom
    (specialLinearDeterminantSquare_isPullback_over K n)
    (generalLinearDeterminantSection_over_comp_det K n pivot)

variable {R : Type u} [CommRing R]

/-- The pivot entry of the diagonal, valued in units before coercion. -/
@[expose] def generalLinearConjDiagonalUnit (pivot : n) (unit : Rˣ) (index : n) : Rˣ :=
  if index = pivot then unit else 1

/-- The native determinant-one diagonal conjugate. -/
def generalLinearDiagonalConjSL (pivot : n) (unit : Rˣ)
    (matrix : Matrix.SpecialLinearGroup n R) : Matrix.SpecialLinearGroup n R := by
  let diagonal := generalLinearDiagonalHom n pivot unit
  let conjugate := diagonal * Matrix.SpecialLinearGroup.toGL matrix * diagonal⁻¹
  have hdet : Matrix.GeneralLinearGroup.det conjugate = 1 := by
    simp [conjugate, diagonal]
  exact ⟨(conjugate : Matrix n n R), congrArg Units.val hdet⟩

/-- The native readback is conjugation inside the existing general-linear group. -/
@[simp] theorem generalLinearDiagonalConjSL_toGL (pivot : n) (unit : Rˣ)
    (matrix : Matrix.SpecialLinearGroup n R) :
    Matrix.SpecialLinearGroup.toGL (generalLinearDiagonalConjSL n pivot unit matrix) =
      generalLinearDiagonalHom n pivot unit * Matrix.SpecialLinearGroup.toGL matrix *
        (generalLinearDiagonalHom n pivot unit)⁻¹ := by
  apply Matrix.GeneralLinearGroup.ext
  intro row col
  rfl

/-- At every affine `K`-algebra point the categorical action agrees with native
diagonal conjugation, rather than merely agreeing on global `K`-points. -/
theorem generalLinearDeterminantConj_point [Algebra K R] (pivot : n) (unit : Rˣ)
    (matrix : Matrix.SpecialLinearGroup n R) :
    lift (multiplicativeGroupMulEquivPoints K R unit)
      (specialLinearGroupMulEquivPoints K n R matrix) ≫
        generalLinearDeterminantConj K n pivot =
      specialLinearGroupMulEquivPoints K n R
        (generalLinearDiagonalConjSL n pivot unit matrix) := by
  apply (specialLinearDeterminantSquare_isPullback_over K n).hom_ext
  · calc
      (lift (multiplicativeGroupMulEquivPoints K R unit)
          (specialLinearGroupMulEquivPoints K n R matrix) ≫
          generalLinearDeterminantConj K n pivot) ≫
          (specialLinearInclusion K n).hom.hom =
        (multiplicativeGroupMulEquivPoints K R unit ≫
            (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom) *
          (specialLinearGroupMulEquivPoints K n R matrix ≫
            (specialLinearInclusion K n).hom.hom) *
          (multiplicativeGroupMulEquivPoints K R unit ≫
            (generalLinearDeterminantSectionSchemeHom K n pivot).hom.hom)⁻¹ := by
              exact splitKernelConj_lift_comp_i _ _ _ _ _ _ _
      _ = generalLinearGroupMulEquivPoints K n R
            (generalLinearDiagonalHom n pivot unit * Matrix.SpecialLinearGroup.toGL matrix *
              (generalLinearDiagonalHom n pivot unit)⁻¹) := by
              rw [generalLinearDeterminantSection_point, specialLinearInclusion_point]
              simp
      _ = specialLinearGroupMulEquivPoints K n R
            (generalLinearDiagonalConjSL n pivot unit matrix) ≫
            (specialLinearInclusion K n).hom.hom := by
              rw [specialLinearInclusion_point, generalLinearDiagonalConjSL_toGL]
  · simp

/-- For any coefficient ring, diagonal conjugation scales entry `(row,col)`
by the row unit and the inverse column unit. The inverse is formed in `Rˣ`
before coercion to `R`; the proof uses Mathlib's `Matrix.diagonal_mul` and
`Matrix.mul_diagonal`, without dividing by an arbitrary ring element. -/
theorem generalLinearDiagonalConjSL_apply (pivot : n) (unit : Rˣ)
    (matrix : Matrix.SpecialLinearGroup n R) (row col : n) :
    generalLinearDiagonalConjSL n pivot unit matrix row col =
      (generalLinearConjDiagonalUnit n pivot unit row : R) * matrix row col *
        (((generalLinearConjDiagonalUnit n pivot unit col)⁻¹ : Rˣ) : R) := by
  have readback := congrArg (fun g : Matrix.GeneralLinearGroup n R ↦ (g : Matrix n n R) row col)
    (generalLinearDiagonalConjSL_toGL n pivot unit matrix)
  have hdiag (value : Rˣ) :
      ((generalLinearDiagonalHom n pivot value : Matrix.GeneralLinearGroup n R) :
        Matrix n n R) =
        Matrix.diagonal (fun index ↦ (generalLinearConjDiagonalUnit n pivot value index : R)) := by
    ext index other
    simp [generalLinearDiagonalHom_apply, generalLinearConjDiagonalUnit,
      Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hinv : (generalLinearConjDiagonalUnit n pivot unit⁻¹ col : R) =
      (((generalLinearConjDiagonalUnit n pivot unit col)⁻¹ : Rˣ) : R) := by
    by_cases hcol : col = pivot <;> simp [generalLinearConjDiagonalUnit, hcol]
  change (generalLinearDiagonalConjSL n pivot unit matrix : Matrix n n R) row col = _
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at readback
  exact readback.trans (by
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [← (generalLinearDiagonalHom n pivot).map_inv unit]
    rw [hdiag, hdiag, Matrix.mul_diagonal, Matrix.diagonal_mul, hinv])

end AlgebraicGeometry
