/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.ExteriorPower.DeterminantLine
public import ProjectiveModules.Module.RightExtensionTensorProduct

/-!
# Determinant classes and extension of right modules

For a finite projective right `R`-module `P`, extension along `f : R →+* S`
has a determinant line over `Sᵐᵒᵖ`. Its Picard class is compared with the image
of the determinant class of `P` under the opposite homomorphism `f.op`.
The extension carrier is `ModuleCat.RightExtension.Obj f P`, with its canonical
right `S`-action. The coefficient and module-carrier universes are independent.
Neither flatness nor a constant stalk rank is required, and the coefficient
rings may be zero rings.

## References

C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, §I.3, for
the determinant construction. The scalar-extension comparison here is derived
from that construction, with independent universes and zero rings permitted.
The Picard-group and
invertible-module interfaces are Mathlib's formalization by Junyan Xu. The
right-module extension and rank-fiber determinant construction are the
formalizations by Formal Frontier Agents in this library.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace ModuleCat.RightExtension

/-- The determinant class of a finite projective right module commutes with
extension of scalars. This comparison is derived from the determinant
construction in C. A. Weibel's *The K-book*, §I.3, using variable local rank
and allowing zero rings and independent coefficient and carrier universes. -/
theorem determinantLine_mk
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Type w) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P] :
    @CommRing.Pic.mk Sᵐᵒᵖ (Module.DeterminantLine Sᵐᵒᵖ (Obj f P))
        _ _ _ (Module.determinantLine_invertible Sᵐᵒᵖ (Obj f P)) =
      CommRing.Pic.mapRingHom f.op
        (@CommRing.Pic.mk Rᵐᵒᵖ (Module.DeterminantLine Rᵐᵒᵖ P)
          _ _ _ (Module.determinantLine_invertible Rᵐᵒᵖ P)) := by
  classical
  -- The ordinary tensor endpoint uses the opposite homomorphism, not `f`.
  letI : Algebra Rᵐᵒᵖ Sᵐᵒᵖ := f.op.toAlgebra
  let Q := Obj f P
  let A := Rᵐᵒᵖ
  let B := Sᵐᵒᵖ
  let L := Module.DeterminantLine A P
  let Y := Module.DeterminantLine B Q
  let X := B ⊗[A] L
  let eQ : Q ≃ₗ[B] B ⊗[A] P :=
    oppositeScalarEquiv f (ModuleCat.of Rᵐᵒᵖ P)
  have hQrank (q : PrimeSpectrum B) :
      Module.rankAtStalk (R := B) Q q =
        Module.rankAtStalk (R := A) P (q.comap f.op) :=
    (congrFun (Module.rankAtStalk_eq_of_equiv eQ) q).trans
      (Module.rankAtStalk_baseChange (R := A) (M := P) q)
  have hcomponents (j : Module.rankFiberIndex B Q) :
      Nonempty ((Module.rankFiberRing B Q j) ⊗[B] X ≃ₗ[B]
        (Module.rankFiberRing B Q j) ⊗[B] Y) := by
    let C := Module.rankFiberRing B Q j
    letI : Algebra A C := ((algebraMap B C).comp f.op).toAlgebra
    letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    -- The coefficient action comes from the composite algebra; the module
    -- action is inherited by the quotient. Compare them through B.
    letI := IsScalarTower.of_algebraMap_smul (R := A) (A := C) (M := C)
      (fun a c => by
        change algebraMap A C a * c = a • c
        rw [← IsScalarTower.algebraMap_smul B a c]
        exact (Algebra.smul_def (algebraMap A B a) c).symm)
    -- A target fiber supplies an attained source rank, even if other source
    -- fibers disappear. No bijection of the two index types is asserted.
    obtain ⟨q₀, hq₀⟩ := Function.Fiber.fiber_nonempty (Module.rankLocallyConstant B Q) j
    let i : Module.rankFiberIndex A P :=
      Function.Fiber.mk (Module.rankLocallyConstant A P) (q₀.comap f.op)
    have hi₀ : q₀.comap f.op ∈ i.1 := rfl
    have hn : Module.rankFiberRank A P i = Module.rankFiberRank B Q j :=
      (Module.rankAtStalk_eq_rankFiberRank_of_mem A P i _ hi₀).symm.trans
        ((hQrank q₀).symm.trans
          (Module.rankAtStalk_eq_rankFiberRank_of_mem B Q j q₀ hq₀))
    -- The source idempotent maps to one on this target component: its image
    -- is idempotent and avoids every prime of the component ring.
    let a : {c : C // IsIdempotentElem c} :=
      ⟨algebraMap A C (Module.rankFiberIdempotent A P i),
        (Module.rankFiberIdempotent_isIdempotent A P i).map (algebraMap A C)⟩
    have ha : PrimeSpectrum.isIdempotentElemEquivClopens a = ⊤ := by
      apply TopologicalSpace.Clopens.ext
      apply Set.eq_univ_of_forall
      intro t
      change algebraMap A C (Module.rankFiberIdempotent A P i) ∉ t.asIdeal
      let q : PrimeSpectrum B := t.comap (algebraMap B C)
      have hq : Module.rankAtStalk (R := B) Q q = Module.rankFiberRank B Q j :=
        (Module.rankAtStalk_baseChange (R := B) (M := Q) t).symm.trans
          (Module.rankAtStalk_rankFiberModule B Q j t)
      have hr : Module.rankAtStalk (R := A) P (t.comap (algebraMap A C)) =
          Module.rankFiberRank A P i := by
        change Module.rankAtStalk (R := A) P (q.comap f.op) = _
        exact (hQrank q).symm.trans (hq.trans hn.symm)
      apply (Module.rankFiberIdempotent_notMem_iff A P i
        (t.comap (algebraMap A C))).2
      apply (Function.Fiber.mem_iff_eq_image (Module.rankLocallyConstant A P) _ i).2
      rw [← (Function.Fiber.mem_iff_eq_image
        (Module.rankLocallyConstant A P) (q₀.comap f.op) i).1 hi₀]
      simpa only [Module.rankLocallyConstant_apply] using
        hr.trans (Module.rankAtStalk_eq_rankFiberRank_of_mem A P i _ hi₀).symm
    have hi : algebraMap A C (Module.rankFiberIdempotent A P i) = 1 := by
      let e := PrimeSpectrum.isIdempotentElemEquivClopens (R := C)
      have h : a = ⟨1, IsIdempotentElem.one⟩ :=
        (e.symm_apply_apply a).symm.trans
          ((congrArg e.symm ha).trans
            PrimeSpectrum.isIdempotentElemEquivClopens_symm_top)
      exact congrArg Subtype.val h
    let eP : (C ⊗[A] P) ≃ₗ[C] (C ⊗[B] Q) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C P).symm.trans
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) eQ.symm)
    have hsource := Module.determinantLine_component_baseChange_congr A P C i hi eP
    rw [hn] at hsource
    obtain ⟨source⟩ := hsource
    obtain ⟨target⟩ := Module.determinantLine_component B Q j
    exact ⟨((TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C L).trans
      (source.trans target.symm)).restrictScalars B⟩
  -- Decompose both modules over the same finite partition of the target
  -- spectrum, then assemble the component comparisons. Empty partitions
  -- work as well; an attained rank-zero component is still present.
  let dX : X ≃ₗ[B] ∀ j : Module.rankFiberIndex B Q,
      (Module.rankFiberRing B Q j) ⊗[B] X :=
    (TensorProduct.lid B X).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr
        (Module.rankFiberRingEquiv B Q).toLinearEquiv
        (LinearEquiv.refl B X)).trans
          (TensorProduct.piLeft B X (fun j : Module.rankFiberIndex B Q ↦
            Module.rankFiberRing B Q j)))
  let dY : Y ≃ₗ[B] ∀ j : Module.rankFiberIndex B Q,
      (Module.rankFiberRing B Q j) ⊗[B] Y :=
    (TensorProduct.lid B Y).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr
        (Module.rankFiberRingEquiv B Q).toLinearEquiv
        (LinearEquiv.refl B Y)).trans
          (TensorProduct.piLeft B Y (fun j : Module.rankFiberIndex B Q ↦
            Module.rankFiberRing B Q j)))
  let e : X ≃ₗ[B] Y :=
    dX.trans ((LinearEquiv.piCongrRight fun j ↦ (hcomponents j).some).trans dY.symm)
  letI : Module.Invertible A L := Module.determinantLine_invertible A P
  letI : Module.Invertible B Y := Module.determinantLine_invertible B Q
  -- The Picard map tensors its small representative, not definitionally `L`.
  -- Its representative equivalence supplies precisely the final bridge.
  change CommRing.Pic.mk B Y =
    CommRing.Pic.mk B (B ⊗[A] CommRing.Pic.AsModule (CommRing.Pic.mk A L))
  apply CommRing.Pic.mk_eq_mk_iff.mpr
  exact ⟨e.symm.trans (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl B B) (CommRing.Pic.mk.linearEquiv A L).symm)⟩

end ModuleCat.RightExtension
