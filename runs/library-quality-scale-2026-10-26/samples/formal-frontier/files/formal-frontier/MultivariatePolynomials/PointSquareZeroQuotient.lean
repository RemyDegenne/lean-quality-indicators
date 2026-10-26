/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import MultivariatePolynomials.PointSquareZeroPresentation

/-!
# Separation of polynomial point coordinates

The equivalence uses the generator-prescribed map from the presentation
module. Pairwise unit differences force mixed coordinate products to vanish;
evaluation-quotient linear maps and the square-zero universal property give
inverse maps.

## References

* Ravi Vakil, *The Rising Sea: Foundations of Algebraic Geometry*, for the
  polynomial point-quotient setting.
* Mathlib's polynomial and ideal-quotient universal properties, and Coherent
  Modules' canonical square-zero action, supply the algebraic interface.
-/

@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι

variable {R : Type uR} {ι : Type uι} [CommRing R]

private theorem pointSquareZero_cross (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) (i j : ι) :
    (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) *
      (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some j))) = 0 := by
  let t (k : ι) : pointSquareZeroQuotient a :=
    Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some k))
  let x : pointSquareZeroQuotient a :=
    Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)
  let c (r : R) : pointSquareZeroQuotient a :=
    Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r)
  change t i * t j = 0
  by_cases hij : i = j
  · subst j
    simpa only [pow_two] using pointSquareZero_sq a i
  have hi : (x - c (a i)) * (t i * t j) = 0 := by
    rw [← mul_assoc, show (x - c (a i)) * t i = 0 from pointSquareZero_linear a i,
      zero_mul]
  have hj : (x - c (a j)) * (t i * t j) = 0 := by
    rw [mul_comm (t i) (t j), ← mul_assoc,
      show (x - c (a j)) * t j = 0 from pointSquareZero_linear a j, zero_mul]
  have hu : IsUnit (algebraMap R (pointSquareZeroQuotient a) (a i - a j)) :=
    (hsep i j hij).map (algebraMap R (pointSquareZeroQuotient a))
  apply hu.mul_left_cancel
  calc
    algebraMap R (pointSquareZeroQuotient a) (a i - a j) * (t i * t j) =
        ((x - c (a j)) - (x - c (a i))) * (t i * t j) := by
          rw [map_sub]
          have hc (r : R) : algebraMap R (pointSquareZeroQuotient a) r = c r := by
            change algebraMap R (pointSquareZeroQuotient a) r =
              Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r)
            rw [← pointSquareZero_algebraMap_C a]
            exact IsScalarTower.algebraMap_apply R R[X] (pointSquareZeroQuotient a) r
          rw [hc, hc]
          ring
    _ = 0 := by rw [sub_mul, hj, hi, sub_self]
    _ = algebraMap R (pointSquareZeroQuotient a) (a i - a j) * 0 := by simp

private noncomputable def pointSquareZeroCoordinate (a : ι → R) (i : ι) :
    (R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i))) →ₗ[R[X]]
      pointSquareZeroQuotient a := by
  let f : R[X] →ₗ[R[X]] pointSquareZeroQuotient a :=
    { toFun := fun p => algebraMap R[X] (pointSquareZeroQuotient a) p *
        Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))
      map_add' := by
        intro p q
        simp only [map_add, add_mul]
      map_smul' := by
        intro p q
        change algebraMap R[X] (pointSquareZeroQuotient a) (p * q) * _ =
          algebraMap R[X] (pointSquareZeroQuotient a) p *
            (algebraMap R[X] (pointSquareZeroQuotient a) q * _)
        rw [map_mul, mul_assoc] }
  apply (RingHom.ker (Polynomial.evalRingHom (a i))).liftQ f
  intro p hp
  have hp' : p ∈ Ideal.span {Polynomial.X - Polynomial.C (a i)} := by
    rw [← Polynomial.ker_evalRingHom (a i)]
    exact hp
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hp'
  have hlinear : algebraMap R[X] (pointSquareZeroQuotient a)
      (Polynomial.X - Polynomial.C (a i)) *
        Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i)) = 0 := by
    rw [map_sub, pointSquareZero_algebraMap_X, pointSquareZero_algebraMap_C]
    exact pointSquareZero_linear a i
  change algebraMap R[X] (pointSquareZeroQuotient a) p * _ = 0
  rw [← hq, map_mul, mul_assoc, hlinear, mul_zero]

@[simp] private theorem pointSquareZeroCoordinate_mk (a : ι → R) (i : ι) (p : R[X]) :
    pointSquareZeroCoordinate a i
      (Ideal.Quotient.mk (RingHom.ker (Polynomial.evalRingHom (a i))) p) =
      algebraMap R[X] (pointSquareZeroQuotient a) p *
        Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i)) := by
  rfl

private noncomputable def pointSquareZeroSum (a : ι → R) [DecidableEq ι] :
    pointSquareZeroModule a →ₗ[R[X]] pointSquareZeroQuotient a :=
  DirectSum.toModule R[X] ι (pointSquareZeroQuotient a)
    (pointSquareZeroCoordinate a)

@[simp] private theorem pointSquareZeroSum_lof (a : ι → R) [DecidableEq ι] (i : ι)
    (b : R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i))) :
    pointSquareZeroSum a
      (DirectSum.lof R[X] ι
        (fun i => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i))) i b) =
        pointSquareZeroCoordinate a i b := by
  classical
  simp only [pointSquareZeroSum, DirectSum.toModule_lof]

/-- Unit differences between distinct evaluation points make the prescribed
map from the polynomial quotient to the canonical square-zero extension
bijective. -/
theorem pointSquareZeroForward_bijective (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) :
    Function.Bijective (pointSquareZeroForward a) := by
  classical
  let g := pointSquareZeroSum a
  have hsingle (i j : ι)
      (b : R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a i)))
      (c : R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a j))) :
      g (DirectSum.lof R[X] ι
          (fun k => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a k))) i b) *
        g (DirectSum.lof R[X] ι
          (fun k => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a k))) j c) = 0 := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective c
    change pointSquareZeroSum a _ * pointSquareZeroSum a _ = 0
    rw [pointSquareZeroSum_lof, pointSquareZeroSum_lof,
      pointSquareZeroCoordinate_mk, pointSquareZeroCoordinate_mk]
    calc
      (algebraMap R[X] (pointSquareZeroQuotient a) p *
          Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) *
          (algebraMap R[X] (pointSquareZeroQuotient a) q *
            Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some j))) =
        algebraMap R[X] (pointSquareZeroQuotient a) p *
          algebraMap R[X] (pointSquareZeroQuotient a) q *
            (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i)) *
              Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some j))) := by ring
      _ = 0 := by rw [pointSquareZero_cross a hsep i j, mul_zero]
  have hg (m n : pointSquareZeroModule a) : g m * g n = 0 := by
    induction m using DirectSum.induction_on with
    | zero => simp
    | of i b =>
      induction n using DirectSum.induction_on with
      | zero => simp
      | of j c => exact hsingle i j b c
      | add m n hm hn => simp only [map_add, mul_add, hm, hn, add_zero]
    | add m n hm hn => simp only [map_add, add_mul, hm, hn, add_zero]
  let reverse : TrivSqZeroExt R[X] (pointSquareZeroModule a) →ₐ[R[X]]
      pointSquareZeroQuotient a := TrivSqZeroExt.liftEquivOfComm ⟨g, hg⟩
  have reverse_inr (m : pointSquareZeroModule a) :
      reverse (TrivSqZeroExt.inr m) = g m := by
    simp [reverse, TrivSqZeroExt.liftEquivOfComm_apply]
  have hleft : reverse.comp (pointSquareZeroForward a) =
      AlgHom.id R[X] (pointSquareZeroQuotient a) := by
    apply pointSquareZeroAlgHom_ext a
    intro i
    rw [AlgHom.comp_apply, pointSquareZeroForward_mk_some, reverse_inr]
    change pointSquareZeroSum a (pointSquareZeroDelta a i) = _
    rw [pointSquareZeroDelta, pointSquareZeroSum_lof, pointSquareZeroCoordinate_mk,
      map_one, one_mul, AlgHom.id_apply]
  have hright : (pointSquareZeroForward a).comp reverse =
      AlgHom.id R[X] (TrivSqZeroExt R[X] (pointSquareZeroModule a)) := by
    apply TrivSqZeroExt.algHom_ext
    intro m
    rw [AlgHom.comp_apply, reverse_inr, AlgHom.id_apply]
    have hdelta (i : ι) (p : R[X]) :
        p • pointSquareZeroDelta a i =
          DirectSum.lof R[X] ι
            (fun k => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a k))) i
            (Ideal.Quotient.mk (RingHom.ker (Polynomial.evalRingHom (a i))) p) := by
      rw [pointSquareZeroDelta, ← map_smul]
      congr 1
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one]
    suffices h : ∀ n : pointSquareZeroModule a,
        pointSquareZeroForward a (g n) = TrivSqZeroExt.inr n from h m
    intro n
    induction n using DirectSum.induction_on with
    | zero => simp
    | of i b =>
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      change pointSquareZeroForward a
        (g (DirectSum.lof R[X] ι
          (fun k => R[X] ⧸ RingHom.ker (Polynomial.evalRingHom (a k))) i _)) = _
      rw [pointSquareZeroSum_lof, pointSquareZeroCoordinate_mk, map_mul,
        (pointSquareZeroForward a).commutes, TrivSqZeroExt.algebraMap_eq_inl,
        pointSquareZeroForward_mk_some, TrivSqZeroExt.inl_mul_inr, hdelta,
        DirectSum.lof_eq_of]
    | add m n hm hn =>
      simp only [map_add, TrivSqZeroExt.inr_add, hm, hn]
  constructor
  · intro x y h
    calc
      x = reverse (pointSquareZeroForward a x) := (AlgHom.congr_fun hleft x).symm
      _ = reverse (pointSquareZeroForward a y) := congrArg reverse h
      _ = y := AlgHom.congr_fun hleft y
  · intro z
    refine ⟨reverse z, ?_⟩
    exact AlgHom.congr_fun hright z

/-- The polynomial point quotient as the canonical square-zero extension of
its evaluation summands, under pairwise unit differences. This equivalence is
the fixed generator-prescribed forward map. -/
noncomputable def pointSquareZeroAlgEquiv (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) :
    pointSquareZeroQuotient a ≃ₐ[R[X]]
      TrivSqZeroExt R[X] (pointSquareZeroModule a) :=
  AlgEquiv.ofBijective (pointSquareZeroForward a)
    (pointSquareZeroForward_bijective a hsep)

@[simp] theorem pointSquareZeroAlgEquiv_mk_some (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) (i : ι) :
    pointSquareZeroAlgEquiv a hsep
      (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i))) =
        TrivSqZeroExt.inr (pointSquareZeroDelta a i) := by
  simpa only [pointSquareZeroAlgEquiv, AlgEquiv.ofBijective_apply] using
    pointSquareZeroForward_mk_some a i

@[simp] theorem pointSquareZeroAlgEquiv_mk_none (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) :
    pointSquareZeroAlgEquiv a hsep
      (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)) =
        TrivSqZeroExt.inl (Polynomial.X : R[X]) := by
  simpa only [pointSquareZeroAlgEquiv, AlgEquiv.ofBijective_apply] using
    pointSquareZeroForward_mk_none a

@[simp] theorem pointSquareZeroAlgEquiv_mk_C (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) (r : R) :
    pointSquareZeroAlgEquiv a hsep
      (Ideal.Quotient.mk (pointSquareZeroIdeal a) (C r)) =
        TrivSqZeroExt.inl (Polynomial.C r : R[X]) := by
  simpa only [pointSquareZeroAlgEquiv, AlgEquiv.ofBijective_apply] using
    pointSquareZeroForward_mk_C a r

@[simp] theorem pointSquareZeroAlgEquiv_symm_delta (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) (i : ι) :
    (pointSquareZeroAlgEquiv a hsep).symm
        (TrivSqZeroExt.inr (pointSquareZeroDelta a i)) =
      Ideal.Quotient.mk (pointSquareZeroIdeal a) (X (some i)) := by
  rw [← pointSquareZeroAlgEquiv_mk_some]
  exact (pointSquareZeroAlgEquiv a hsep).symm_apply_apply _

end MvPolynomial
