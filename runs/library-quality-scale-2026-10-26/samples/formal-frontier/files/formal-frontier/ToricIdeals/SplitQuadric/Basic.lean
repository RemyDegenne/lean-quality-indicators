/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic

/-!
# The coordinate algebra and charts of the split quadric

For an arbitrary commutative ring `A`, the relation is `w * z - x * y = 0`.
The polynomial parametrization sends `(w, x, y, z)` to `(W, W * T, Y, Y * T)`,
with target coordinates in the order `W, Y, T`. Its quotient morphism `phi`
is constructed just from determinant vanishing.

The quotient universal property and the comparison of the charts where `w`
and `W` are invertible need no domain, nontriviality or global surjectivity
hypothesis. The chart morphisms and their inverse identities are independent
of the global kernel theorem. In the zero-ring case both parametrizations are
surjective; for nontrivial coefficients the range is not the entire target.

## References

Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry* (October 21, 2025),
§4.4, motivates the determinant model. Mathlib supplies polynomial evaluation,
quotient algebra homomorphisms, and localization universal properties. The
formalization of this model and its charts is by Formal Frontier Agents.
-/

@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

/-- Polynomials in `w, x, y, z`, in this order. -/
abbrev Polynomial := MvPolynomial (Fin 4) A

/-- Polynomials in `W, Y, T`, in this order. -/
abbrev ParameterPolynomial := MvPolynomial (Fin 3) A

/-- The determinant of the matrix with rows `(w, x)` and `(y, z)`. -/
def relation : Polynomial A :=
  MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 1 * MvPolynomial.X 2

/-- The principal relation ideal. -/
def relationIdeal : Ideal (Polynomial A) := Ideal.span {relation A}

/-- The split quadric coordinate algebra over `A`, including the zero ring case. -/
abbrev CoordinateRing := Polynomial A ⧸ relationIdeal A

/-- The quotient projection as an `A`-algebra homomorphism. -/
def quotientMap : Polynomial A →ₐ[A] CoordinateRing A :=
  Ideal.Quotient.mkₐ A (relationIdeal A)

/-- The coefficient homomorphism. -/
def coefficientMap : A →+* CoordinateRing A := algebraMap A (CoordinateRing A)

/-- A coordinate class in the quotient. -/
def coordinate (i : Fin 4) : CoordinateRing A := quotientMap A (MvPolynomial.X i)

abbrev w : CoordinateRing A := coordinate A 0
abbrev x : CoordinateRing A := coordinate A 1
abbrev y : CoordinateRing A := coordinate A 2
abbrev z : CoordinateRing A := coordinate A 3

abbrev W : ParameterPolynomial A := MvPolynomial.X 0
abbrev Y : ParameterPolynomial A := MvPolynomial.X 1
abbrev T : ParameterPolynomial A := MvPolynomial.X 2

@[simp]
theorem quotientMap_C (a : A) : quotientMap A (MvPolynomial.C a) = coefficientMap A a := rfl

@[simp]
theorem quotientMap_X (i : Fin 4) : quotientMap A (MvPolynomial.X i) = coordinate A i := rfl

/-- The defining relation holds without assumptions on the coefficient ring. -/
theorem coordinate_relation : w A * z A - x A * y A = 0 := by
  change quotientMap A (MvPolynomial.X 0) * quotientMap A (MvPolynomial.X 3) -
    quotientMap A (MvPolynomial.X 1) * quotientMap A (MvPolynomial.X 2) = 0
  rw [← map_mul, ← map_mul, ← map_sub]
  change Ideal.Quotient.mk (relationIdeal A) (relation A) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

section UniversalMorphism

variable {S : Type v} [CommRing S] [Algebra A S]

/-- Killing the displayed determinant kills its ideal; this is only a constructor helper. -/
theorem relationIdeal_le_ker_aeval (values : Fin 4 → S)
    (h : values 0 * values 3 - values 1 * values 2 = 0) :
    relationIdeal A ≤ RingHom.ker (MvPolynomial.aeval values).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  have hp' : p = relation A := Set.mem_singleton_iff.mp hp
  subst p
  change MvPolynomial.aeval values (relation A) = 0
  simpa [relation] using h

/-- An assignment satisfying the determinant equation induces a quotient morphism. -/
def lift (values : Fin 4 → S) (h : values 0 * values 3 - values 1 * values 2 = 0) :
    CoordinateRing A →ₐ[A] S :=
  Ideal.Quotient.liftₐ (relationIdeal A) (MvPolynomial.aeval values)
    (fun _ hp => relationIdeal_le_ker_aeval A values h hp)

@[simp]
theorem lift_quotientMap (values : Fin 4 → S)
    (h : values 0 * values 3 - values 1 * values 2 = 0) (p : Polynomial A) :
    lift A values h (quotientMap A p) = MvPolynomial.aeval values p := rfl

@[simp]
theorem lift_coordinate (values : Fin 4 → S)
    (h : values 0 * values 3 - values 1 * values 2 = 0) (i : Fin 4) :
    lift A values h (coordinate A i) = values i := by
  simp only [coordinate, lift_quotientMap, MvPolynomial.aeval_X]

@[simp]
theorem lift_coefficientMap (values : Fin 4 → S)
    (h : values 0 * values 3 - values 1 * values 2 = 0) (a : A) :
    lift A values h (coefficientMap A a) = algebraMap A S a :=
  (lift A values h).commutes a

/-- Algebra morphisms out of the quadric are determined by its four coordinates. -/
@[ext]
theorem hom_ext {f g : CoordinateRing A →ₐ[A] S}
    (h : ∀ i, f (coordinate A i) = g (coordinate A i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

/-- The universal morphism recovers any morphism from its coordinate values. -/
theorem lift_unique (f : CoordinateRing A →ₐ[A] S)
    (values : Fin 4 → S) (h : values 0 * values 3 - values 1 * values 2 = 0)
    (hf : ∀ i, f (coordinate A i) = values i) : f = lift A values h := by
  apply hom_ext A
  intro i
  simpa using hf i

end UniversalMorphism

/-- The four images defining the parametrization. -/
def parameterValues : Fin 4 → ParameterPolynomial A := ![W A, W A * T A, Y A, Y A * T A]

/-- The polynomial parametrization. -/
def theta : Polynomial A →ₐ[A] ParameterPolynomial A := MvPolynomial.aeval (parameterValues A)

@[simp]
theorem theta_X (i : Fin 4) : theta A (MvPolynomial.X i) = parameterValues A i := by
  simp [theta]

@[simp]
theorem theta_C (a : A) : theta A (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [theta]

/-- The determinant vanishes under the chosen assignment. -/
theorem parameterValues_relation :
    parameterValues A 0 * parameterValues A 3 - parameterValues A 1 * parameterValues A 2 = 0 := by
  change W A * (Y A * T A) - (W A * T A) * Y A = 0
  ring

/-- The induced quotient parametrization; its construction does not use the kernel equality. -/
def phi : CoordinateRing A →ₐ[A] ParameterPolynomial A :=
  lift A (parameterValues A) (parameterValues_relation A)

@[simp]
theorem phi_quotientMap (p : Polynomial A) : phi A (quotientMap A p) = theta A p := rfl

@[simp]
theorem phi_coefficientMap (a : A) : phi A (coefficientMap A a) = MvPolynomial.C a :=
  (phi A).commutes a

@[simp]
theorem phi_coordinate (i : Fin 4) : phi A (coordinate A i) = parameterValues A i :=
  lift_coordinate A _ _ i

@[simp] theorem phi_w : phi A (w A) = W A := by simp [w, parameterValues]
@[simp] theorem phi_x : phi A (x A) = W A * T A := by simp [x, parameterValues]
@[simp] theorem phi_y : phi A (y A) = Y A := by simp [y, parameterValues]
@[simp] theorem phi_z : phi A (z A) = Y A * T A := by simp [z, parameterValues]

/-! ## The chart where `w` is invertible

The two base rings are different. The comparison is a localized `phi`, with an
explicit inverse assignment; it is not a same-base uniqueness equivalence.
-/

section Chart

variable (LQ : Type s) [CommRing LQ]
  [Algebra (CoordinateRing A) LQ] [Algebra A LQ]
  [IsScalarTower A (CoordinateRing A) LQ] [IsLocalization.Away (w A) LQ]

/-- The inverse polynomial assignment `W, Y, T ↦ w, y, x / w` in any model of the chart. -/
noncomputable def inversePolynomial : ParameterPolynomial A →ₐ[A] LQ :=
  MvPolynomial.aeval ![algebraMap (CoordinateRing A) LQ (w A),
    algebraMap (CoordinateRing A) LQ (y A),
    algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A)]

omit [IsScalarTower A (CoordinateRing A) LQ] in
/-- The inverse polynomial assignment on each variable. -/
@[simp]
theorem inversePolynomial_X (i : Fin 3) :
    inversePolynomial A LQ (MvPolynomial.X i) =
      ![algebraMap (CoordinateRing A) LQ (w A),
        algebraMap (CoordinateRing A) LQ (y A),
        algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A)] i := by
  simp only [inversePolynomial, MvPolynomial.aeval_X]

omit [IsScalarTower A (CoordinateRing A) LQ] in
@[simp]
theorem inversePolynomial_W :
    inversePolynomial A LQ (W A) = algebraMap (CoordinateRing A) LQ (w A) := by
  simp [inversePolynomial, W]

omit [IsScalarTower A (CoordinateRing A) LQ] in
@[simp]
theorem inversePolynomial_Y :
    inversePolynomial A LQ (Y A) = algebraMap (CoordinateRing A) LQ (y A) := by
  simp [inversePolynomial, Y]

omit [IsScalarTower A (CoordinateRing A) LQ] in
@[simp]
theorem inversePolynomial_T : inversePolynomial A LQ (T A) =
    algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A) := by
  simp [inversePolynomial, T]

variable (LB : Type t) [CommRing LB]
  [Algebra (ParameterPolynomial A) LB] [Algebra A LB]
  [IsScalarTower A (ParameterPolynomial A) LB] [IsLocalization.Away (W A) LB]

/-- Localize the quotient parametrization. No injectivity or domain hypothesis is required. -/
noncomputable def chartForward : LQ →ₐ[A] LB := by
  letI : IsLocalization.Away (phi A (w A)) LB := by
    rw [phi_w]
    infer_instance
  exact IsLocalization.Away.mapₐ LQ LB (phi A) (w A)

omit [IsScalarTower A (CoordinateRing A) LQ] in
/-- Extend the inverse assignment by the universal property of localization. -/
noncomputable def chartBackward : LB →ₐ[A] LQ :=
  IsLocalization.Away.liftAlgHom (f := inversePolynomial A LQ) (W A)
    (show IsUnit (inversePolynomial A LQ (W A)) from by
      simpa using (IsLocalization.Away.algebraMap_isUnit (S := LQ) (w A)))

/-- The square with the two localization maps commutes. -/
theorem chartForward_algebraMap (q : CoordinateRing A) :
    chartForward A LQ LB (algebraMap (CoordinateRing A) LQ q) =
      algebraMap (ParameterPolynomial A) LB (phi A q) := by
  simp only [chartForward, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

omit [IsScalarTower A (CoordinateRing A) LQ] in
/-- The inverse agrees with its polynomial assignment. -/
theorem chartBackward_algebraMap (b : ParameterPolynomial A) :
    chartBackward A LQ LB (algebraMap (ParameterPolynomial A) LB b) =
      inversePolynomial A LQ b := by
  simp only [chartBackward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The constructed morphisms are inverse on the parameter chart. -/
theorem chartForward_comp_chartBackward :
    (chartForward A LQ LB).comp (chartBackward A LQ LB) = AlgHom.id A LB := by
  -- The image of the inverse of `w` cancels `W`, without a nonzero premise.
  have hw : algebraMap (ParameterPolynomial A) LB (W A) *
      chartForward A LQ LB (IsLocalization.Away.invSelf (w A)) = 1 := by
    simpa only [map_mul, map_one, chartForward_algebraMap, phi_w] using
      congrArg (chartForward A LQ LB) (IsLocalization.Away.mul_invSelf (S := LQ) (w A))
  apply IsLocalization.algHom_ext (Submonoid.powers (W A))
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.algHom,
    IsScalarTower.toAlgHom_apply]
  fin_cases i
  · simp only [chartBackward_algebraMap, inversePolynomial_X, Matrix.cons_val_zero',
      chartForward_algebraMap, phi_w]
    rfl
  · simp only [chartBackward_algebraMap, inversePolynomial_X, Matrix.cons_val_succ',
      Matrix.cons_val_zero', chartForward_algebraMap, phi_y]
    rfl
  · simp only [chartBackward_algebraMap, inversePolynomial_X, Matrix.cons_val_succ',
      Matrix.cons_val_zero', map_mul, chartForward_algebraMap, phi_x]
    calc
      (algebraMap (ParameterPolynomial A) LB (W A) * algebraMap (ParameterPolynomial A) LB (T A)) *
          chartForward A LQ LB (IsLocalization.Away.invSelf (w A)) =
          algebraMap (ParameterPolynomial A) LB (T A) *
            (algebraMap (ParameterPolynomial A) LB (W A) *
              chartForward A LQ LB (IsLocalization.Away.invSelf (w A))) := by ring
      _ = algebraMap (ParameterPolynomial A) LB (T A) := by rw [hw, mul_one]

/-- The constructed morphisms are inverse on the quadric chart. -/
theorem chartBackward_comp_chartForward :
    (chartBackward A LQ LB).comp (chartForward A LQ LB) = AlgHom.id A LQ := by
  have hw : algebraMap (CoordinateRing A) LQ (w A) * IsLocalization.Away.invSelf (w A) = 1 :=
    IsLocalization.Away.mul_invSelf (S := LQ) (w A)
  have hrel : algebraMap (CoordinateRing A) LQ (w A) * algebraMap (CoordinateRing A) LQ (z A) =
      algebraMap (CoordinateRing A) LQ (x A) * algebraMap (CoordinateRing A) LQ (y A) := by
    apply sub_eq_zero.mp
    simpa only [map_sub, map_mul, map_zero] using
      congrArg (algebraMap (CoordinateRing A) LQ) (coordinate_relation A)
  apply IsLocalization.algHom_ext (Submonoid.powers (w A))
  apply hom_ext A
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, Algebra.algHom,
    IsScalarTower.toAlgHom_apply]
  fin_cases i
  · simp only [chartForward_algebraMap, phi_coordinate, parameterValues, Matrix.cons_val_zero',
      chartBackward_algebraMap, inversePolynomial_W]
    rfl
  · simp only [chartForward_algebraMap, phi_coordinate, parameterValues, Matrix.cons_val_succ',
      Matrix.cons_val_zero', chartBackward_algebraMap, map_mul, inversePolynomial_W,
      inversePolynomial_T]
    calc
      algebraMap (CoordinateRing A) LQ (w A) *
          (algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A)) =
          algebraMap (CoordinateRing A) LQ (x A) *
            (algebraMap (CoordinateRing A) LQ (w A) * IsLocalization.Away.invSelf (w A)) := by ring
      _ = algebraMap (CoordinateRing A) LQ (x A) := by rw [hw, mul_one]
  · simp only [chartForward_algebraMap, phi_coordinate, parameterValues, Matrix.cons_val_succ',
      Matrix.cons_val_zero', chartBackward_algebraMap, inversePolynomial_Y]
    rfl
  · simp only [chartForward_algebraMap, phi_coordinate, parameterValues, Matrix.cons_val_succ',
      Matrix.cons_val_zero', chartBackward_algebraMap, map_mul, inversePolynomial_Y,
      inversePolynomial_T]
    calc
      algebraMap (CoordinateRing A) LQ (y A) *
          (algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A)) =
          (algebraMap (CoordinateRing A) LQ (x A) * algebraMap (CoordinateRing A) LQ (y A)) *
            IsLocalization.Away.invSelf (w A) := by ring
      _ = (algebraMap (CoordinateRing A) LQ (w A) * algebraMap (CoordinateRing A) LQ (z A)) *
          IsLocalization.Away.invSelf (w A) := by rw [← hrel]
      _ = algebraMap (CoordinateRing A) LQ (z A) *
          (algebraMap (CoordinateRing A) LQ (w A) * IsLocalization.Away.invSelf (w A)) := by ring
      _ = algebraMap (CoordinateRing A) LQ (z A) := by rw [hw, mul_one]

/-- The chart equivalence, using the inverse identities and explicit morphisms. -/
noncomputable def chartEquiv : LQ ≃ₐ[A] LB :=
  AlgEquiv.ofAlgHom (chartForward A LQ LB) (chartBackward A LQ LB)
    (chartForward_comp_chartBackward A LQ LB) (chartBackward_comp_chartForward A LQ LB)

@[simp]
theorem chartEquiv_apply (q : LQ) : chartEquiv A LQ LB q = chartForward A LQ LB q := rfl

@[simp]
theorem chartEquiv_symm_apply (b : LB) :
    (chartEquiv A LQ LB).symm b = chartBackward A LQ LB b := rfl

/-- The four forward generator equations, from the commuting localization square. -/
theorem chartEquiv_generators :
    chartEquiv A LQ LB (algebraMap (CoordinateRing A) LQ (w A)) =
        algebraMap (ParameterPolynomial A) LB (W A) ∧
    chartEquiv A LQ LB (algebraMap (CoordinateRing A) LQ (x A)) =
        algebraMap (ParameterPolynomial A) LB (W A * T A) ∧
    chartEquiv A LQ LB (algebraMap (CoordinateRing A) LQ (y A)) =
        algebraMap (ParameterPolynomial A) LB (Y A) ∧
    chartEquiv A LQ LB (algebraMap (CoordinateRing A) LQ (z A)) =
        algebraMap (ParameterPolynomial A) LB (Y A * T A) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [chartEquiv_apply, chartForward_algebraMap, phi_w, phi_x, phi_y, phi_z]

/-- The three inverse generator equations, from the inverse polynomial assignment. -/
theorem chartEquiv_inverse_generators :
    (chartEquiv A LQ LB).symm (algebraMap (ParameterPolynomial A) LB (W A)) =
        algebraMap (CoordinateRing A) LQ (w A) ∧
    (chartEquiv A LQ LB).symm (algebraMap (ParameterPolynomial A) LB (Y A)) =
        algebraMap (CoordinateRing A) LQ (y A) ∧
    (chartEquiv A LQ LB).symm (algebraMap (ParameterPolynomial A) LB (T A)) =
        algebraMap (CoordinateRing A) LQ (x A) * IsLocalization.Away.invSelf (w A) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [chartEquiv_symm_apply, chartBackward_algebraMap, inversePolynomial_W,
      inversePolynomial_Y, inversePolynomial_T]

end Chart

/-- The canonical localization models of the chart. No nonzero or global-unit premise is needed. -/
noncomputable def canonicalChartEquiv :
    Localization.Away (w A) ≃ₐ[A] Localization.Away (W A) :=
  chartEquiv A (Localization.Away (w A)) (Localization.Away (W A))

end SplitQuadric
