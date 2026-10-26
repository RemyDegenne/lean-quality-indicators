/-
Licensed under the Apache License, Version 2.0 (see LICENSE).
Authors: Formal Frontier Agents
-/
module

public import NormForms.HomogeneousSystemZeros
public import MultivariatePolynomials.LinearCoefficientEvaluation
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Homogeneous-form zeros over algebraic field extensions

The all-positive-degree single-form zero bound passes from a field to any algebraic
extension. Finite-basis polynomial coordinates and the finite coefficient field
are internal to the proof.
-/

set_option warningAsError true
set_option linter.style.haveILetI false

namespace MvPolynomial

private theorem finite_extension_form_zero {k E : Type*} [Field k] [Field E]
    [Algebra k E] [FiniteDimensional k E] (r : ℕ)
    (hsingle : ∀ (a t : ℕ) (p : MvPolynomial (Fin t) k),
      0 < a → a ^ r < t → p.IsHomogeneous a →
        ∃ x : Fin t → k, x ≠ 0 ∧ eval x p = 0)
    (d n : ℕ) (hd : 0 < d) (hsize : d ^ r < n)
    (f : MvPolynomial (Fin n) E) (hf : f.IsHomogeneous d) :
    ∃ x : Fin n → E, x ≠ 0 ∧ eval x f = 0 := by
  classical
  let t := Module.finrank k E
  let b : Module.Basis (Fin t) k E := Module.finBasis k E
  have ht : 0 < t := (Module.finrank_pos_iff_of_free k E).mpr inferInstance
  let substitutedVariables : Fin n → MvPolynomial (Fin n × Fin t) E :=
    fun index => ∑ coordinate : Fin t,
      C (b coordinate) * X (index, coordinate)
  let substituted : MvPolynomial (Fin n × Fin t) E :=
    eval₂ C substitutedVariables f
  let coordinates : Fin t → MvPolynomial (Fin n × Fin t) k :=
    fun coordinate => AddMonoidAlgebra.map (b.coord coordinate).toAddMonoidHom substituted
  have hvars (index : Fin n) : (substitutedVariables index).IsHomogeneous 1 := by
    exact IsHomogeneous.sum _ _ _ (fun coordinate _ =>
      isHomogeneous_C_mul_X (b coordinate) (index, coordinate))
  have hsub : substituted.IsHomogeneous d := by
    simpa only [one_mul] using hf.eval₂ C substitutedVariables
      (fun coefficient => isHomogeneous_C _ coefficient) hvars
  have hcoordinates (coordinate : Fin t) : (coordinates coordinate).IsHomogeneous d := by
    intro monomial hmonomial
    apply hsub
    intro hzero
    apply hmonomial
    simp [coordinates, hzero]
  let flattened : Fin n × Fin t ≃ Fin (n * t) := finProdFinEquiv
  let equations : Fin t → MvPolynomial (Fin (n * t)) k :=
    fun coordinate => rename flattened (coordinates coordinate)
  have hequations (coordinate : Fin t) : (equations coordinate).IsHomogeneous d :=
    (hcoordinates coordinate).rename_isHomogeneous
  have hbound : t * d ^ r < n * t := by
    simpa only [mul_comm] using Nat.mul_lt_mul_of_pos_right hsize ht
  obtain ⟨flatPoint, hflatPoint, hflatZero⟩ :=
    exists_nonzero_common_zero_of_single_form_bound r hsingle d t (n * t)
      hd hbound equations hequations
  let point : Fin n × Fin t → k := fun index => flatPoint (flattened index)
  have hpoint : point ≠ 0 := by
    intro hzero
    apply hflatPoint
    funext index
    have hi := congrFun hzero (flattened.symm index)
    simpa only [point, Equiv.apply_symm_apply, Pi.zero_apply] using hi
  have hcoordinateZero (coordinate : Fin t) : eval point (coordinates coordinate) = 0 := by
    have hzero := hflatZero coordinate
    simpa only [equations, eval_rename, Function.comp_def, point] using hzero
  let extensionPoint : Fin n → E := fun index =>
    b.equivFun.symm (fun coordinate => point (index, coordinate))
  have hevaluation :
      eval (algebraMap k E ∘ point) substituted = eval extensionPoint f := by
    dsimp only [substituted]
    rw [eval_eval₂]
    have hevalC : (eval (algebraMap k E ∘ point)).comp C = RingHom.id E := by
      ext coefficient
      simp
    rw [hevalC, eval₂_id]
    have hpoints :
        (fun index => eval (algebraMap k E ∘ point) (substitutedVariables index)) =
          extensionPoint := by
      funext index
      simp only [substitutedVariables, eval_sum, eval_mul, eval_C, eval_X,
        Function.comp_apply, extensionPoint, Module.Basis.equivFun_symm_apply,
        Algebra.smul_def]
      apply Finset.sum_congr rfl
      intro coordinate _
      exact mul_comm _ _
    rw [hpoints]
  have hzero : eval extensionPoint f = 0 := by
    rw [← hevaluation]
    apply (b.forall_coord_eq_zero_iff).mp
    intro coordinate
    simpa only [coordinates] using
      (eval_addMonoidAlgebraMap_of_linearMap (b.coord coordinate) substituted point).trans
        (hcoordinateZero coordinate)
  refine ⟨extensionPoint, ?_, hzero⟩
  intro hzeroPoint
  apply hpoint
  funext index
  have hcoordinate := congrArg (b.coord index.2) (congrFun hzeroPoint index.1)
  simpa only [extensionPoint, Module.Basis.coord_equivFun_symm,
    Pi.zero_apply, map_zero] using hcoordinate

public section

/-- A uniform positive-degree homogeneous single-form zero bound over a field
passes unchanged to any algebraic extension of that field. -/
theorem exists_nonzero_zero_of_isAlgebraic_of_single_form_bound
    {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (r : ℕ)
    (hsingle : ∀ (a t : ℕ) (p : MvPolynomial (Fin t) k),
      0 < a → a ^ r < t → p.IsHomogeneous a →
        ∃ x : Fin t → k, x ≠ 0 ∧ eval x p = 0)
    (d n : ℕ) (hd : 0 < d) (hsize : d ^ r < n)
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x f = 0 := by
  classical
  let coefficientField : IntermediateField k K :=
    IntermediateField.adjoin k (f.coeffs : Set K)
  haveI : FiniteDimensional k coefficientField :=
    IntermediateField.finiteDimensional_adjoin
      (fun coefficient _ => (Algebra.IsAlgebraic.isIntegral (K := k)).1 coefficient)
  let inclusion : coefficientField →+* K := algebraMap coefficientField K
  have hinclusion : Function.Injective inclusion := inclusion.injective
  have hcoefficients : (f.coeffs : Set K) ⊆ Set.range inclusion := by
    intro coefficient hcoefficient
    refine ⟨⟨coefficient, IntermediateField.subset_adjoin k _ hcoefficient⟩, ?_⟩
    rfl
  obtain ⟨lift, hlift⟩ := (mem_range_map_iff_coeffs_subset (f := inclusion)).mpr
    hcoefficients
  have hliftHomogeneous : lift.IsHomogeneous d := by
    apply IsHomogeneous.of_map hinclusion
    simpa only [hlift] using hf
  obtain ⟨point, hpoint, hzero⟩ :=
    finite_extension_form_zero r hsingle d n hd hsize lift hliftHomogeneous
  refine ⟨inclusion ∘ point, ?_, ?_⟩
  · intro hzeroPoint
    apply hpoint
    funext index
    apply hinclusion
    simpa only [Function.comp_apply, map_zero, Pi.zero_apply] using
      congrFun hzeroPoint index
  · have htransport := map_eval inclusion point lift
    simpa only [hlift, map_zero] using htransport.symm.trans (congrArg inclusion hzero)

end

end MvPolynomial
