/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Fredholm polynomials of finite projective endomorphisms

A finite projective module is a direct summand of a finite free module.  This
file associates to an endomorphism its reverse characteristic polynomial in
any such finite-free presentation.  The rectangular Weinstein--Aronszajn
identity `Matrix.det_one_sub_mul_comm` proves that the result is independent
of the presentation.  It also proves scalar-base-change and intertwining
formulas.

This construction deliberately does not construct or specialize a
fixed-degree exterior-power base-change equivalence; it uses split finite-free
presentations instead. The construction does not require constant rank.

## References

* Mathlib, `Mathlib.LinearAlgebra.Matrix.SchurComplement`, proves the
  Weinstein--Aronszajn identity `Matrix.det_one_sub_mul_comm` used to compare
  rectangular split presentations. `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`
  defines `Matrix.charpolyRev`, the determinant `det(1 - X f)` on a finite free
  module.
* Mathlib, `Mathlib.RingTheory.Finiteness.Projective`
  (`Module.Finite.exists_comp_eq_id_of_projective`) supplies a finite-free split
  presentation, and `Mathlib.LinearAlgebra.TensorProduct.Free` supplies the
  finite-basis scalar-extension equivalence.
-/

public section

noncomputable section

open Polynomial

namespace Module.FiniteProjective

universe uR uM

variable (R : Type uR) (M : Type uM)
  [CommRing R] [AddCommGroup M] [Module R M]

/-- A realization of a module as a split direct summand of a finite free
module. -/
structure FreePresentation where
  /-- The rank of the ambient finite free module. -/
  n : ℕ
  /-- The split projection from the ambient finite free module. -/
  proj : (Fin n → R) →ₗ[R] M
  /-- The inclusion into the ambient finite free module. -/
  incl : M →ₗ[R] Fin n → R
  /-- The projection is a left inverse to the inclusion. -/
  proj_comp_incl : proj ∘ₗ incl = LinearMap.id

/-- A chosen finite-free split presentation of a finite projective module. -/
noncomputable def freePresentation [Module.Finite R M] [Module.Projective R M] :
    FreePresentation R M := by
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.2.2⟩

/-- The Fredholm polynomial `det(1 - X f)` computed in a finite-free split
presentation. -/
@[expose] noncomputable def FreePresentation.fredholm (P : FreePresentation R M)
    (f : Module.End R M) : R[X] :=
  Matrix.charpolyRev (LinearMap.toMatrix'
    (P.incl.comp (f.comp P.proj)))

/-- The Fredholm polynomial is independent of the finite-free split
presentation by Mathlib's Weinstein--Aronszajn identity
`Matrix.det_one_sub_mul_comm`. This includes presentations of different
finite ranks. -/
lemma FreePresentation.fredholm_eq (P Q : FreePresentation R M)
    (f : Module.End R M) :
    FreePresentation.fredholm (R := R) (M := M) P f =
      FreePresentation.fredholm (R := R) (M := M) Q f := by
  let A : Matrix (Fin P.n) (Fin Q.n) R := LinearMap.toMatrix'
    (P.incl.comp (f.comp Q.proj))
  let B : Matrix (Fin Q.n) (Fin P.n) R := LinearMap.toMatrix'
    (Q.incl.comp P.proj)
  have hcompAB :
      (P.incl.comp (f.comp Q.proj)).comp (Q.incl.comp P.proj) =
        P.incl.comp (f.comp P.proj) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    exact congrArg (fun y ↦ P.incl (f y)) <| by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun Q.proj_comp_incl (P.proj x)
  have hcompBA :
      (Q.incl.comp P.proj).comp (P.incl.comp (f.comp Q.proj)) =
        Q.incl.comp (f.comp Q.proj) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    exact congrArg Q.incl <| by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun P.proj_comp_incl (f (Q.proj x))
  have hAB : A * B = LinearMap.toMatrix' (P.incl.comp (f.comp P.proj)) := by
    rw [← LinearMap.toMatrix'_comp, hcompAB]
  have hBA : B * A = LinearMap.toMatrix' (Q.incl.comp (f.comp Q.proj)) := by
    rw [← LinearMap.toMatrix'_comp, hcompBA]
  simp only [FreePresentation.fredholm, Matrix.charpolyRev]
  rw [← hAB, ← hBA]
  let AX : Matrix (Fin P.n) (Fin Q.n) R[X] := (X : R[X]) • A.map C
  let BC : Matrix (Fin Q.n) (Fin P.n) R[X] := B.map C
  calc
    Matrix.det (1 - (X : R[X]) • (A * B).map C) =
        Matrix.det (1 - AX * BC) := by simp [AX, BC, Matrix.smul_mul]
    _ = Matrix.det (1 - BC * AX) := Matrix.det_one_sub_mul_comm AX BC
    _ = Matrix.det (1 - (X : R[X]) • (B * A).map C) := by
      simp [AX, BC, Matrix.mul_smul]

universe uS

/-- Scalar extension of a finite-free split presentation. -/
noncomputable def FreePresentation.baseChange (P : FreePresentation R M)
    (S : Type uS) [CommRing S] [Algebra R S] :
    FreePresentation S (TensorProduct R S M) := by
  let e : TensorProduct R S (Fin P.n → R) ≃ₗ[S] (Fin P.n → S) :=
    Algebra.TensorProduct.equivPiOfFiniteBasis S (Pi.basisFun R (Fin P.n))
  refine
    { n := P.n
      proj := (P.proj.baseChange S).comp e.symm.toLinearMap
      incl := e.toLinearMap.comp (P.incl.baseChange S)
      proj_comp_incl := ?_ }
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp_all
  | tmul s x =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
        LinearMap.id_apply]
      rw [show P.proj (P.incl x) = x by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun P.proj_comp_incl x]

/-- Fredholm polynomials commute with arbitrary scalar extension. The finite
free matrix comparison uses Mathlib's `Matrix.charpolyRev` and
`Algebra.TensorProduct.equivPiOfFiniteBasis`. -/
lemma FreePresentation.fredholm_baseChange (P : FreePresentation R M)
    (S : Type uS) [CommRing S] [Algebra R S]
    (f : Module.End R M) :
    (FreePresentation.fredholm (R := R) (M := M) P f).map (algebraMap R S) =
      FreePresentation.fredholm (R := S) (M := TensorProduct R S M)
        (FreePresentation.baseChange (R := R) (M := M) P S) (f.baseChange S) := by
  let e : TensorProduct R S (Fin P.n → R) ≃ₗ[S] (Fin P.n → S) :=
    Algebra.TensorProduct.equivPiOfFiniteBasis S (Pi.basisFun R (Fin P.n))
  have he_symm (j : Fin P.n) :
      e.symm (Pi.single j 1) = (1 : S) ⊗ₜ[R] Pi.single j 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext i
    simp [e, Algebra.TensorProduct.equivPiOfFiniteBasis,
      Pi.basisFun_equivFun, Pi.single_apply]
  have hmatrix :
      LinearMap.toMatrix'
        ((FreePresentation.baseChange (R := R) (M := M) P S).incl.comp
          ((f.baseChange S).comp
            (FreePresentation.baseChange (R := R) (M := M) P S).proj)) =
        (LinearMap.toMatrix' (P.incl.comp (f.comp P.proj))).map
          (algebraMap R S) := by
    dsimp only [FreePresentation.baseChange]
    ext i j
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
    change e ((P.incl.baseChange S)
      ((f.baseChange S) ((P.proj.baseChange S) (e.symm (Pi.single j 1))))) i = _
    rw [he_symm]
    simp [e, Algebra.TensorProduct.equivPiOfFiniteBasis,
      Pi.basisFun_equivFun, Algebra.smul_def]
  unfold FreePresentation.fredholm
  simp only [Matrix.charpolyRev]
  change (Polynomial.mapRingHom (algebraMap R S))
      (Matrix.det (1 - (X : R[X]) •
        (LinearMap.toMatrix' (P.incl.comp (f.comp P.proj))).map C)) = _
  rw [RingHom.map_det]
  rw [hmatrix]
  congr 1
  apply Matrix.ext
  intro i j
  change (Polynomial.mapRingHom (algebraMap R S))
      ((if i = j then (1 : R[X]) else 0) - X *
        C (P.incl (f (P.proj (Pi.single j 1))) i)) =
    ((if i = j then (1 : S[X]) else 0) - X *
      C ((algebraMap R S) (P.incl (f (P.proj (Pi.single j 1))) i)))
  by_cases h : i = j <;> simp [h]

universe uN

/-- Intertwining equivalent endomorphisms have the same Fredholm polynomial,
even when computed in unrelated split presentations. -/
lemma FreePresentation.fredholm_eq_of_equiv_intertwine
    {N : Type uN} [AddCommGroup N] [Module R N]
    (P : FreePresentation R M) (Q : FreePresentation R N)
    (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (h : e.toLinearMap.comp f = g.comp e.toLinearMap) :
    FreePresentation.fredholm (R := R) (M := M) P f =
      FreePresentation.fredholm (R := R) (M := N) Q g := by
  let A : Matrix (Fin P.n) (Fin Q.n) R := LinearMap.toMatrix'
    (P.incl.comp (f.comp (e.symm.toLinearMap.comp Q.proj)))
  let B : Matrix (Fin Q.n) (Fin P.n) R := LinearMap.toMatrix'
    (Q.incl.comp (e.toLinearMap.comp P.proj))
  have hcompAB :
      (P.incl.comp (f.comp (e.symm.toLinearMap.comp Q.proj))).comp
          (Q.incl.comp (e.toLinearMap.comp P.proj)) =
        P.incl.comp (f.comp P.proj) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    have hq : Q.proj (Q.incl (e (P.proj x))) = e (P.proj x) := by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun Q.proj_comp_incl (e (P.proj x))
    simpa using congrArg (fun y ↦ P.incl (f (e.symm y))) hq
  have hcompBA :
      (Q.incl.comp (e.toLinearMap.comp P.proj)).comp
          (P.incl.comp (f.comp (e.symm.toLinearMap.comp Q.proj))) =
        Q.incl.comp (g.comp Q.proj) := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    have hp : P.proj (P.incl (f (e.symm (Q.proj x)))) =
        f (e.symm (Q.proj x)) := by
      simpa [LinearMap.comp_apply] using
        LinearMap.congr_fun P.proj_comp_incl (f (e.symm (Q.proj x)))
    calc
      Q.incl (e (P.proj (P.incl (f (e.symm (Q.proj x)))))) =
          Q.incl (e (f (e.symm (Q.proj x)))) :=
        congrArg (fun y ↦ Q.incl (e y)) hp
      _ = Q.incl (g (Q.proj x)) := by
        have hi := LinearMap.congr_fun h (e.symm (Q.proj x))
        simpa [LinearMap.comp_apply] using congrArg Q.incl hi
  have hAB : A * B = LinearMap.toMatrix' (P.incl.comp (f.comp P.proj)) := by
    rw [← LinearMap.toMatrix'_comp, hcompAB]
  have hBA : B * A = LinearMap.toMatrix' (Q.incl.comp (g.comp Q.proj)) := by
    rw [← LinearMap.toMatrix'_comp, hcompBA]
  simp only [FreePresentation.fredholm, Matrix.charpolyRev]
  rw [← hAB, ← hBA]
  let AX : Matrix (Fin P.n) (Fin Q.n) R[X] := (X : R[X]) • A.map C
  let BC : Matrix (Fin Q.n) (Fin P.n) R[X] := B.map C
  calc
    Matrix.det (1 - (X : R[X]) • (A * B).map C) =
        Matrix.det (1 - AX * BC) := by simp [AX, BC, Matrix.smul_mul]
    _ = Matrix.det (1 - BC * AX) := Matrix.det_one_sub_mul_comm AX BC
    _ = Matrix.det (1 - (X : R[X]) • (B * A).map C) := by
      simp [AX, BC, Matrix.mul_smul]

end Module.FiniteProjective
