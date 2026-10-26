/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.GeneralLinearCoordinateRing
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Upper-unitriangular coordinate algebras

The quotient of the localized general linear coordinate algebra by the entries
below the diagonal and the diagonal entries minus one is a Hopf algebra. The
coideal condition is proved after applying both quotient maps to the coproduct;
no flatness of the base ring is needed.

The determinant becomes one in the corresponding unlocalized polynomial
quotient. Both this presentation and the polynomial algebra on the strict
upper pairs are compared to the GL quotient as `K`-algebras. These comparisons
do not identify the represented group scheme with an additive group scheme
or assert compatibility with Hopf structures. The represented group law
still has a cross term in rank three.

## References

* J. S. Milne, *Algebraic Groups* (2017), items 2.8–2.9, pp. 41–42:
  the determinant-localized coordinates of `GL_n` and the unlocalized
  polynomial quotient representing `U_n` on commutative algebras.
* Mathlib, `Mathlib/LinearAlgebra/Matrix/Block.lean` (triangular inverses and
  determinants) and Robert Hawkins's Hopf-ideal and quotient formalization
  in `Mathlib/RingTheory/HopfAlgebra/Quotient.lean`.
* `AlgebraicGroups/Algebra/GeneralLinearCoordinateRing.lean` supplies the GL
  Hopf operations; `AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean`
  supplies the earlier localized-to-polynomial quotient proof pattern. The
  lower-entry and diagonal-generator calculations here are separate.
-/

@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing
open scoped TensorProduct

universe u

namespace UnitriangularCoordinateRing

variable (K : Type u) [CommRing K] (ι : Type u) [Fintype ι] [LinearOrder ι]

/-- Each relation is either a lower entry, a diagonal entry minus one, or zero. -/
def relation (i j : ι) : GeneralLinearCoordinateRing.CoordinateRing K ι :=
  if j < i then matrix K ι i j else if i = j then matrix K ι i j - 1 else 0

/-- The defining ideal in the actual, determinant-localized GL coordinate ring. -/
def ideal : Ideal (GeneralLinearCoordinateRing.CoordinateRing K ι) :=
  Ideal.span (Set.range fun p : ι × ι => relation K ι p.1 p.2)

/-- Coordinate algebra of the upper-unitriangular group. -/
abbrev CoordinateRing := GeneralLinearCoordinateRing.CoordinateRing K ι ⧸ ideal K ι

/-- The canonical quotient of the published GL coordinate algebra. -/
def quotient : GeneralLinearCoordinateRing.CoordinateRing K ι →ₐ[K] CoordinateRing K ι :=
  Ideal.Quotient.mkₐ K (ideal K ι)

theorem relation_mem (i j : ι) : relation K ι i j ∈ ideal K ι :=
  Ideal.subset_span ⟨(i, j), rfl⟩

theorem quotient_lower (i j : ι) (h : j < i) : quotient K ι (matrix K ι i j) = 0 := by
  have hz : quotient K ι (relation K ι i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (relation_mem K ι i j)
  simpa [relation, h] using hz

theorem quotient_diag (i : ι) : quotient K ι (matrix K ι i i) = 1 := by
  have hz : quotient K ι (relation K ι i i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (relation_mem K ι i i)
  simpa [relation, map_sub, map_one, sub_eq_zero] using hz

/-- The universal matrix over the quotient, as an invertible native matrix. -/
def universal : Matrix.GeneralLinearGroup ι (CoordinateRing K ι) :=
  Matrix.GeneralLinearGroup.map (quotient K ι).toRingHom
    (GeneralLinearCoordinateRing.universal K ι)

@[simp] theorem universal_apply (i j : ι) : universal K ι i j =
    quotient K ι (matrix K ι i j) := rfl

theorem universal_upper : ((universal K ι) : Matrix ι ι (CoordinateRing K ι)).IsUpperTriangular :=
  fun _ _ hij => quotient_lower K ι _ _ hij

theorem universal_diag (i : ι) : universal K ι i i = 1 := quotient_diag K ι i

@[simp] theorem quotient_detInverse : quotient K ι (detInverse K ι) = 1 := by
  have hdet : quotient K ι (matrix K ι).det = 1 := by
    rw [AlgHom.map_det]
    change ((universal K ι : Matrix ι ι (CoordinateRing K ι))).det = 1
    rw [Matrix.det_of_isUpperTriangular (universal_upper K ι)]
    simp only [universal_apply, quotient_diag, Finset.prod_const_one]
  have hm := congrArg (quotient K ι) (det_mul_detInverse K ι)
  rw [map_mul, map_one, hdet, one_mul] at hm
  exact hm

variable {K ι}

/-- The diagonal of a product of upper-triangular matrices is the product of
their diagonal entries. -/
theorem upper_mul_diag {R : Type u} [CommRing R]
    {a b : Matrix ι ι R} (ha : a.IsUpperTriangular) (hb : b.IsUpperTriangular)
    (i : ι) : (a * b) i i = a i i * b i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [ha hji, zero_mul]
    · rw [hb hij, mul_zero]
  · simp

variable (K ι)

/-- The relations defining Milne's `U_n` (item 2.9) form a Hopf ideal over any
commutative ring. Both quotient maps are applied in the coideal calculation;
antipode stability uses the inverse of the quotient universal GL unit and the
diagonal-of-product identity, rather than a field-point argument. -/
theorem ideal_isHopfIdeal_proof : (ideal K ι).IsHopfIdeal K := by
  let q := quotient K ι
  let comulQuotient : GeneralLinearCoordinateRing.CoordinateRing K ι →ₐ[K]
      CoordinateRing K ι ⊗[K] CoordinateRing K ι :=
    (Algebra.TensorProduct.map q q).comp
      (Bialgebra.comulAlgHom K (GeneralLinearCoordinateRing.CoordinateRing K ι))
  let : CommRing (CoordinateRing K ι ⊗[K] CoordinateRing K ι) := inferInstance
  have counit_gen (i j : ι) :
      (Bialgebra.counitAlgHom K (GeneralLinearCoordinateRing.CoordinateRing K ι))
        (relation K ι i j) = 0 := by
    by_cases hji : j < i
    · have hne : i ≠ j := ne_of_gt hji
      simp only [relation, hji, ↓reduceIte] at *
      change Coalgebra.counit (R := K) (matrix K ι i j) = 0
      rw [native_counit_matrix]
      simp [hne]
    · by_cases hij : i = j
      · subst j
        simp only [relation, lt_irrefl] at *
        change (Bialgebra.counitAlgHom K _) (matrix K ι i i - 1) = 0
        rw [map_sub, map_one, sub_eq_zero]
        change Coalgebra.counit (R := K) (matrix K ι i i) = 1
        simpa [Matrix.one_apply] using native_counit_matrix K ι i i
      · simp [relation, hji, hij]
  have comul_gen (i j : ι) : comulQuotient (relation K ι i j) = 0 := by
    by_cases hji : j < i
    · simp only [relation, hji, ↓reduceIte]
      change (Algebra.TensorProduct.map q q)
        (Coalgebra.comul (R := K) (matrix K ι i j)) = 0
      rw [native_comul_matrix, map_sum]
      apply Finset.sum_eq_zero
      intro index _
      rw [Algebra.TensorProduct.map_tmul]
      by_cases hki : index < i
      · rw [quotient_lower K ι i index hki, TensorProduct.zero_tmul]
      · have hjk : j < index := lt_of_lt_of_le hji (le_of_not_gt hki)
        rw [quotient_lower K ι index j hjk, TensorProduct.tmul_zero]
    · by_cases hij : i = j
      · subst j
        simp only [relation, lt_irrefl] at *
        change comulQuotient (matrix K ι i i - 1) = 0
        rw [map_sub, map_one, sub_eq_zero]
        change (Algebra.TensorProduct.map q q)
          (Coalgebra.comul (R := K) (matrix K ι i i)) = 1
        rw [native_comul_matrix, map_sum]
        have hs : (∑ k : ι, (Algebra.TensorProduct.map q q)
            (matrix K ι i k ⊗ₜ[K] matrix K ι k i)) =
            (Algebra.TensorProduct.map q q)
            (matrix K ι i i ⊗ₜ[K] matrix K ι i i) := by
          apply Finset.sum_eq_single i
          · intro k _ hki
            rw [Algebra.TensorProduct.map_tmul]
            rcases lt_or_gt_of_ne hki with hki | hik
            · rw [quotient_lower K ι i k hki, TensorProduct.zero_tmul]
            · rw [quotient_lower K ι k i hik, TensorProduct.tmul_zero]
          · simp
        rw [hs, Algebra.TensorProduct.map_tmul, quotient_diag, Algebra.TensorProduct.one_def]
      · simp [relation, hji, hij]
  have antipode_gen (i j : ι) :
      HopfAlgebra.antipode K (relation K ι i j) ∈ ideal K ι := by
    have hinv : ((universal K ι)⁻¹ : Matrix.GeneralLinearGroup ι (CoordinateRing K ι)) =
        Matrix.GeneralLinearGroup.map q.toRingHom
          ((GeneralLinearCoordinateRing.universal K ι)⁻¹) := by
      exact ((Matrix.GeneralLinearGroup.map q.toRingHom).map_inv _).symm
    have hinv_upper :
        (((universal K ι)⁻¹ : Matrix.GeneralLinearGroup ι (CoordinateRing K ι)) :
          Matrix ι ι (CoordinateRing K ι)).IsUpperTriangular := by
      have : Invertible (universal K ι : Matrix ι ι (CoordinateRing K ι)) :=
        Units.invertible (universal K ι)
      simpa only [Matrix.GeneralLinearGroup.coe_inv] using
        Matrix.blockTriangular_inv_of_blockTriangular (universal_upper K ι)
    have hinv_diag (k : ι) : (universal K ι)⁻¹ k k = 1 := by
      have h := upper_mul_diag (universal_upper K ι) hinv_upper k
      have hm := congrArg (fun g : Matrix.GeneralLinearGroup ι (CoordinateRing K ι) =>
          (g : Matrix ι ι (CoordinateRing K ι)) k k) (mul_inv_cancel (universal K ι))
      simpa only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
        Matrix.one_apply, ite_true, universal_diag, one_mul] using h.symm.trans hm
    have hantipode (a b : ι) : q (HopfAlgebra.antipode K (matrix K ι a b)) =
        (universal K ι)⁻¹ a b := by
      rw [native_antipode_matrix]
      have heq := congrArg (fun g : Matrix.GeneralLinearGroup ι (CoordinateRing K ι) =>
        (g : Matrix ι ι (CoordinateRing K ι)) a b) hinv
      exact heq.symm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    by_cases hji : j < i
    · simp only [relation, hji, ↓reduceIte] at ⊢
      change q (HopfAlgebra.antipode K (matrix K ι i j)) = 0
      rw [hantipode]
      exact hinv_upper hji
    · by_cases hij : i = j
      · subst j
        simp only [relation, lt_irrefl] at ⊢
        change q (HopfAlgebra.antipode K (matrix K ι i i - 1)) = 0
        change q ((HopfAlgebra.antipodeAlgHom K
          (GeneralLinearCoordinateRing.CoordinateRing K ι)) (matrix K ι i i - 1)) = 0
        rw [map_sub, map_one, map_sub, map_one]
        change q (HopfAlgebra.antipode K (matrix K ι i i)) - 1 = 0
        rw [hantipode, hinv_diag, sub_self]
      · simp [relation, hji, hij]
  refine { counit_eq_zero := ?_, map_mkQ_comul_eq_zero := ?_, antipode_mem := ?_ }
  · intro x hx
    have h : ideal K ι ≤
        RingHom.ker (Bialgebra.counitAlgHom K
          (GeneralLinearCoordinateRing.CoordinateRing K ι)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (counit_gen i j)
    change (Bialgebra.counitAlgHom K
      (GeneralLinearCoordinateRing.CoordinateRing K ι)) x = 0
    exact RingHom.mem_ker.mp (h hx)
  · intro x hx
    have h : ideal K ι ≤ RingHom.ker comulQuotient.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (comul_gen i j)
    exact RingHom.mem_ker.mp (h hx)
  · intro x hx
    have h : ideal K ι ≤
        (ideal K ι).comap (HopfAlgebra.antipodeAlgHom K
          (GeneralLinearCoordinateRing.CoordinateRing K ι)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact antipode_gen i j
    exact h hx

instance ideal_isHopfIdeal : (ideal K ι).IsHopfIdeal K :=
  ideal_isHopfIdeal_proof K ι

/-- Defining equations before localizing the determinant. -/
def polynomialRelation (i j : ι) : PolynomialRing K ι :=
  if j < i then MvPolynomial.X (i, j)
  else if i = j then MvPolynomial.X (i, j) - 1 else 0

def polynomialIdeal : Ideal (PolynomialRing K ι) :=
  Ideal.span (Set.range fun p : ι × ι => polynomialRelation K ι p.1 p.2)

/-- The unlocalized polynomial presentation. -/
abbrev PolynomialCoordinateRing := PolynomialRing K ι ⧸ polynomialIdeal K ι

def polynomialQuotient : PolynomialRing K ι →ₐ[K] PolynomialCoordinateRing K ι :=
  Ideal.Quotient.mkₐ K (polynomialIdeal K ι)

omit [Fintype ι] in
theorem polynomialQuotient_lower (i j : ι) (h : j < i) :
    polynomialQuotient K ι (MvPolynomial.X (i, j)) = 0 := by
  have hz : polynomialQuotient K ι (polynomialRelation K ι i j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, j), rfl⟩)
  simpa [polynomialRelation, h] using hz

omit [Fintype ι] in
theorem polynomialQuotient_diag (i : ι) :
    polynomialQuotient K ι (MvPolynomial.X (i, i)) = 1 := by
  have hz : polynomialQuotient K ι (polynomialRelation K ι i i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(i, i), rfl⟩)
  simpa [polynomialRelation, map_sub, map_one, sub_eq_zero] using hz

/-- The generic polynomial matrix has determinant one, even in the zero ring. -/
theorem polynomialQuotient_det : polynomialQuotient K ι (determinant K ι) = 1 := by
  rw [determinant, AlgHom.map_det]
  change ((Matrix.mvPolynomialX ι ι K).map (polynomialQuotient K ι)).det = 1
  have hup : ((Matrix.mvPolynomialX ι ι K).map
      (polynomialQuotient K ι)).IsUpperTriangular := by
    intro i j h
    exact polynomialQuotient_lower K ι i j h
  rw [Matrix.det_of_isUpperTriangular hup]
  simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, polynomialQuotient_diag,
    Finset.prod_const_one]

/-- Localization descends after the determinant becomes the unit one. -/
def localizationToPolynomialQuotient :
    GeneralLinearCoordinateRing.CoordinateRing K ι →ₐ[K] PolynomialCoordinateRing K ι :=
  IsLocalization.Away.liftAlgHom (determinant K ι)
    (f := polynomialQuotient K ι) (by
      rw [polynomialQuotient_det]
      exact isUnit_one)

/-- The entry map in the direction from all-entry polynomials to the GL quotient. -/
def polynomialToCoordinateRing : PolynomialRing K ι →ₐ[K] CoordinateRing K ι :=
  (quotient K ι).comp
    (IsScalarTower.toAlgHom K (PolynomialRing K ι)
      (GeneralLinearCoordinateRing.CoordinateRing K ι))

@[simp] theorem polynomialToCoordinateRing_variable (i j : ι) :
    polynomialToCoordinateRing K ι (MvPolynomial.X (i, j)) =
      quotient K ι (matrix K ι i j) := rfl

theorem polynomialToCoordinateRing_relation (i j : ι) :
    polynomialToCoordinateRing K ι (polynomialRelation K ι i j) = 0 := by
  by_cases hji : j < i
  · simp only [polynomialRelation, hji, ↓reduceIte, polynomialToCoordinateRing_variable]
    exact quotient_lower K ι i j hji
  · by_cases hij : i = j
    · subst j
      simp only [polynomialRelation, lt_irrefl, ite_false, ite_true, map_sub, map_one,
        polynomialToCoordinateRing_variable, quotient_diag, sub_self]
    · simp [polynomialRelation, hji, hij]

def polynomialQuotientToCoordinateRing :
    PolynomialCoordinateRing K ι →ₐ[K] CoordinateRing K ι :=
  Ideal.Quotient.liftₐ (polynomialIdeal K ι) (polynomialToCoordinateRing K ι) (by
    intro x hx
    have h : polynomialIdeal K ι ≤
        RingHom.ker (polynomialToCoordinateRing K ι).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (polynomialToCoordinateRing_relation K ι i j)
    exact RingHom.mem_ker.mp (h hx))

@[simp] theorem localizationToPolynomialQuotient_variable (i j : ι) :
    localizationToPolynomialQuotient K ι (matrix K ι i j) =
      polynomialQuotient K ι (MvPolynomial.X (i, j)) := by
  simp only [matrix_apply, localizationToPolynomialQuotient,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe]
  rfl

theorem localizationToPolynomialQuotient_relation (i j : ι) :
    localizationToPolynomialQuotient K ι (relation K ι i j) = 0 := by
  by_cases hji : j < i
  · simp only [relation, hji, ↓reduceIte, localizationToPolynomialQuotient_variable]
    exact polynomialQuotient_lower K ι i j hji
  · by_cases hij : i = j
    · subst j
      simp only [relation, lt_irrefl, ite_false, ite_true, map_sub, map_one,
        localizationToPolynomialQuotient_variable, polynomialQuotient_diag, sub_self]
    · simp [relation, hji, hij]

def coordinateRingToPolynomialQuotient :
    CoordinateRing K ι →ₐ[K] PolynomialCoordinateRing K ι :=
  Ideal.Quotient.liftₐ (ideal K ι) (localizationToPolynomialQuotient K ι) (by
    intro x hx
    have h : ideal K ι ≤
        RingHom.ker (localizationToPolynomialQuotient K ι).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (localizationToPolynomialQuotient_relation K ι i j)
    exact RingHom.mem_ker.mp (h hx))

theorem coordinateRingToPolynomialQuotient_comp_quotient :
    (coordinateRingToPolynomialQuotient K ι).comp (quotient K ι) =
      localizationToPolynomialQuotient K ι :=
  Ideal.Quotient.liftₐ_comp _ _ _

theorem polynomialQuotientToCoordinateRing_comp_polynomialQuotient :
    (polynomialQuotientToCoordinateRing K ι).comp (polynomialQuotient K ι) =
      polynomialToCoordinateRing K ι :=
  Ideal.Quotient.liftₐ_comp _ _ _

theorem coordinateRingToPolynomialQuotient_comp_polynomialQuotientTo :
    (coordinateRingToPolynomialQuotient K ι).comp
      (polynomialQuotientToCoordinateRing K ι) =
      AlgHom.id K (PolynomialCoordinateRing K ι) := by
  apply Ideal.Quotient.algHom_ext K
  rw [AlgHom.comp_assoc]
  change (coordinateRingToPolynomialQuotient K ι).comp
    ((polynomialQuotientToCoordinateRing K ι).comp (polynomialQuotient K ι)) =
      (AlgHom.id K (PolynomialCoordinateRing K ι)).comp (polynomialQuotient K ι)
  rw [polynomialQuotientToCoordinateRing_comp_polynomialQuotient]
  apply MvPolynomial.algHom_ext
  intro ⟨i, j⟩
  change (coordinateRingToPolynomialQuotient K ι)
    (quotient K ι (matrix K ι i j)) =
      (polynomialQuotient K ι) (MvPolynomial.X (i, j))
  rw [← AlgHom.comp_apply, coordinateRingToPolynomialQuotient_comp_quotient]
  exact localizationToPolynomialQuotient_variable K ι i j

theorem polynomialQuotientToCoordinateRing_comp_coordinateRingTo :
    (polynomialQuotientToCoordinateRing K ι).comp
      (coordinateRingToPolynomialQuotient K ι) =
      AlgHom.id K (CoordinateRing K ι) := by
  apply Ideal.Quotient.algHom_ext K
  rw [AlgHom.comp_assoc]
  change (polynomialQuotientToCoordinateRing K ι).comp
    ((coordinateRingToPolynomialQuotient K ι).comp (quotient K ι)) =
      (AlgHom.id K (CoordinateRing K ι)).comp (quotient K ι)
  rw [coordinateRingToPolynomialQuotient_comp_quotient]
  apply IsLocalization.algHom_ext (Submonoid.powers (determinant K ι))
  apply MvPolynomial.algHom_ext
  intro ⟨i, j⟩
  change (polynomialQuotientToCoordinateRing K ι)
    ((localizationToPolynomialQuotient K ι) (matrix K ι i j)) =
      (quotient K ι) (matrix K ι i j)
  rw [localizationToPolynomialQuotient_variable]
  rw [← AlgHom.comp_apply, polynomialQuotientToCoordinateRing_comp_polynomialQuotient]
  exact polynomialToCoordinateRing_variable K ι i j

/-- The GL Hopf quotient and the all-entry polynomial presentation of Milne's
`U_n` (item 2.9) agree as `K`-algebras over any commutative ring, not just on
field-valued points. No compatibility with Hopf structures is asserted. -/
def polynomialEquiv : PolynomialCoordinateRing K ι ≃ₐ[K] CoordinateRing K ι :=
  AlgEquiv.ofAlgHom (polynomialQuotientToCoordinateRing K ι)
    (coordinateRingToPolynomialQuotient K ι)
    (polynomialQuotientToCoordinateRing_comp_coordinateRingTo K ι)
    (coordinateRingToPolynomialQuotient_comp_polynomialQuotientTo K ι)

/-- The same bridge oriented from the localized Hopf quotient to the
all-entry polynomial quotient. -/
def coordinatePolynomialEquiv : CoordinateRing K ι ≃ₐ[K] PolynomialCoordinateRing K ι :=
  (polynomialEquiv K ι).symm

@[simp] theorem polynomialEquiv_variable (i j : ι) :
    polynomialEquiv K ι (polynomialQuotient K ι (MvPolynomial.X (i, j))) =
      quotient K ι (matrix K ι i j) :=
  polynomialToCoordinateRing_variable K ι i j

@[simp] theorem polynomialEquiv_symm_detInverse :
    (polynomialEquiv K ι).symm (quotient K ι (detInverse K ι)) = 1 := by
  rw [quotient_detInverse, map_one]

@[simp] theorem coordinatePolynomialEquiv_entry (i j : ι) :
    coordinatePolynomialEquiv K ι (quotient K ι (matrix K ι i j)) =
      polynomialQuotient K ι (MvPolynomial.X (i, j)) := by
  apply (polynomialEquiv K ι).injective
  change (polynomialEquiv K ι)
    ((polynomialEquiv K ι).symm (quotient K ι (matrix K ι i j))) = _
  rw [AlgEquiv.apply_symm_apply, polynomialEquiv_variable]

@[simp] theorem coordinatePolynomialEquiv_detInverse :
    coordinatePolynomialEquiv K ι (quotient K ι (detInverse K ι)) = 1 :=
  polynomialEquiv_symm_detInverse K ι

/-- The independent coordinates are precisely the strictly upper pairs. -/
abbrev StrictUpperPair := { p : ι × ι // p.1 < p.2 }

/-- The free algebra of strictly upper matrix entries. -/
abbrev FreeCoordinateRing := MvPolynomial (StrictUpperPair ι) K

/-- The generic upper-unitriangular entry over the free algebra. -/
def freeEntry (i j : ι) : FreeCoordinateRing K ι :=
  if h : i < j then MvPolynomial.X ⟨(i, j), h⟩ else if i = j then 1 else 0

omit [Fintype ι] in
@[simp] theorem freeEntry_lower (i j : ι) (h : j < i) : freeEntry K ι i j = 0 := by
  simp [freeEntry, not_lt.mpr (le_of_lt h), ne_of_gt h]

omit [Fintype ι] in
@[simp] theorem freeEntry_diag (i : ι) : freeEntry K ι i i = 1 := by
  simp [freeEntry]

def polynomialToFree : PolynomialRing K ι →ₐ[K] FreeCoordinateRing K ι :=
  MvPolynomial.aeval (fun p : ι × ι => freeEntry K ι p.1 p.2)

omit [Fintype ι] in
@[simp] theorem polynomialToFree_variable (i j : ι) :
    polynomialToFree K ι (MvPolynomial.X (i, j)) = freeEntry K ι i j :=
  MvPolynomial.aeval_X _ _

omit [Fintype ι] in
theorem polynomialToFree_relation (i j : ι) :
    polynomialToFree K ι (polynomialRelation K ι i j) = 0 := by
  by_cases hji : j < i
  · simp only [polynomialRelation, hji, ↓reduceIte, polynomialToFree_variable,
      freeEntry_lower K ι i j hji]
  · by_cases hij : i = j
    · subst j
      simp only [polynomialRelation, lt_irrefl, ite_false, ite_true, map_sub,
        map_one, polynomialToFree_variable, freeEntry_diag, sub_self]
    · simp [polynomialRelation, hji, hij]

def polynomialQuotientToFree : PolynomialCoordinateRing K ι →ₐ[K] FreeCoordinateRing K ι :=
  Ideal.Quotient.liftₐ (polynomialIdeal K ι) (polynomialToFree K ι) (by
    intro x hx
    have h : polynomialIdeal K ι ≤ RingHom.ker (polynomialToFree K ι).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact RingHom.mem_ker.mpr (polynomialToFree_relation K ι i j)
    exact RingHom.mem_ker.mp (h hx))

def freeToPolynomialQuotient : FreeCoordinateRing K ι →ₐ[K] PolynomialCoordinateRing K ι :=
  MvPolynomial.aeval (fun p : StrictUpperPair ι =>
    polynomialQuotient K ι (MvPolynomial.X p.val))

omit [Fintype ι] in
@[simp] theorem freeToPolynomialQuotient_variable (p : StrictUpperPair ι) :
    freeToPolynomialQuotient K ι (MvPolynomial.X p) =
      polynomialQuotient K ι (MvPolynomial.X p.val) :=
  MvPolynomial.aeval_X _ _

omit [Fintype ι] in
theorem polynomialQuotientToFree_comp_freeToPolynomialQuotient :
    (polynomialQuotientToFree K ι).comp (freeToPolynomialQuotient K ι) =
      AlgHom.id K (FreeCoordinateRing K ι) := by
  apply MvPolynomial.algHom_ext
  intro ⟨⟨i, j⟩, hij⟩
  simp only [AlgHom.comp_apply, AlgHom.id_apply, freeToPolynomialQuotient_variable]
  change (polynomialQuotientToFree K ι)
    (polynomialQuotient K ι (MvPolynomial.X (i, j))) = MvPolynomial.X ⟨(i, j), hij⟩
  change (polynomialToFree K ι) (MvPolynomial.X (i, j)) = _
  rw [polynomialToFree_variable]
  simp [freeEntry, hij]

omit [Fintype ι] in
theorem freeToPolynomialQuotient_comp_polynomialQuotientToFree :
    (freeToPolynomialQuotient K ι).comp (polynomialQuotientToFree K ι) =
      AlgHom.id K (PolynomialCoordinateRing K ι) := by
  apply Ideal.Quotient.algHom_ext K
  change ((freeToPolynomialQuotient K ι).comp (polynomialToFree K ι)) =
    polynomialQuotient K ι
  apply MvPolynomial.algHom_ext
  intro ⟨i, j⟩
  simp only [AlgHom.comp_apply, polynomialToFree_variable]
  change (freeToPolynomialQuotient K ι) (freeEntry K ι i j) =
    polynomialQuotient K ι (MvPolynomial.X (i, j))
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [freeEntry, hij, freeToPolynomialQuotient_variable]
  · subst j
    simp [freeEntry, polynomialQuotient_diag]
  · simp [freeEntry, not_lt.mpr (le_of_lt hij), ne_of_gt hij,
      polynomialQuotient_lower K ι i j hij]

/-- The unlocalized all-entry presentation of Milne's `U_n` (item 2.9) is
the free polynomial algebra on exactly the strictly upper entries. This
algebra equivalence does not assert an additive-group-scheme identification
or compatibility with Hopf structures. -/
def polynomialFreeEquiv : PolynomialCoordinateRing K ι ≃ₐ[K] FreeCoordinateRing K ι :=
  AlgEquiv.ofAlgHom (polynomialQuotientToFree K ι)
    (freeToPolynomialQuotient K ι)
    (polynomialQuotientToFree_comp_freeToPolynomialQuotient K ι)
    (freeToPolynomialQuotient_comp_polynomialQuotientToFree K ι)

/-- The localized Hopf quotient is a freely generated polynomial algebra
on the strictly upper entries, as a `K`-algebra. This combines the
unlocalized presentation of Milne's `U_n` (item 2.9) with determinant
localization; it does not identify the Hopf structure with an additive one. -/
def freeEquiv : FreeCoordinateRing K ι ≃ₐ[K] CoordinateRing K ι :=
  (polynomialFreeEquiv K ι).symm.trans (polynomialEquiv K ι)

@[simp] theorem freeEquiv_variable (p : StrictUpperPair ι) :
    freeEquiv K ι (MvPolynomial.X p) = quotient K ι (matrix K ι p.1.1 p.1.2) := by
  change (polynomialEquiv K ι)
    ((freeToPolynomialQuotient K ι) (MvPolynomial.X p)) = _
  rw [freeToPolynomialQuotient_variable, polynomialEquiv_variable]

instance finiteType : Algebra.FiniteType K (CoordinateRing K ι) :=
  Algebra.FiniteType.of_surjective (quotient K ι) Ideal.Quotient.mk_surjective

end UnitriangularCoordinateRing
