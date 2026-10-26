/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberMixedCommutator

/-!
# Mixed commutators in the native special linear group over iterated dual numbers

For trace-zero matrices, both infinitesimal factors belong to the native special linear
group. Their ordered commutator is an element of the outer reduction kernel, whose
readback is the pure-inner image of the special linear Lie bracket.
-/

@[expose] public section
set_option warningAsError true

universe u v

namespace Matrix.DualNumberMixedSLCommutator

open Matrix.DualNumberKernels Matrix.DualNumberMixedCommutator

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The pure-inner coefficient of a trace-zero matrix is itself trace zero. -/
def innerPureSL (X : LieAlgebra.SpecialLinear.sl n R) :
    LieAlgebra.SpecialLinear.sl n (DualNumber R) :=
  ⟨innerPure X.1, by
    change (innerPure X.1).trace = 0
    have h : (X.1 : Matrix n n R).trace = 0 := X.property
    change ((X.1 : Matrix n n R).map (TrivSqZeroExt.inrHom R R)).trace = 0
    rw [← AddMonoidHom.map_trace, h, map_zero]⟩

/-- Outer-constant embedding of the native inner special-linear infinitesimal. -/
def epsilonLiftSL (X : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup n (DualNumber (DualNumber R)) :=
  Matrix.SpecialLinearGroup.map
    (algebraMap (DualNumber R) (DualNumber (DualNumber R))) (liftSL X)

/-- Native outer special-linear infinitesimal with inner-constant coefficient. -/
def etaLiftSL (Y : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup n (DualNumber (DualNumber R)) :=
  liftSL (slMap (algebraMap R (DualNumber R)) Y)

/-- The epsilon factor's underlying matrix is the outer-constant inner lift. -/
@[simp] theorem epsilonLiftSL_val (X : LieAlgebra.SpecialLinear.sl n R) :
    (epsilonLiftSL X : Matrix n n (DualNumber (DualNumber R))) =
      (liftMatrix X.1).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))) := rfl

/-- The eta factor's underlying matrix is the outer lift of inner constants. -/
@[simp] theorem etaLiftSL_val (Y : LieAlgebra.SpecialLinear.sl n R) :
    (etaLiftSL Y : Matrix n n (DualNumber (DualNumber R))) =
      liftMatrix (innerConstant Y.1) := by
  change liftMatrix (slMap (algebraMap R (DualNumber R)) Y).1 = _
  rw [slMap_val]
  rfl

/-- Whole-group inclusion identifies epsilon with the accepted native GL factor. -/
theorem epsilonLiftSL_toGL (X : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup.toGL (epsilonLiftSL X) = epsilonLiftGL X.1 := by
  apply Units.ext
  exact epsilonLiftSL_val X

/-- Whole-group inclusion identifies eta with the accepted native GL factor. -/
theorem etaLiftSL_toGL (Y : LieAlgebra.SpecialLinear.sl n R) :
    Matrix.SpecialLinearGroup.toGL (etaLiftSL Y) = etaLiftGL Y.1 := by
  apply Units.ext
  exact etaLiftSL_val Y

/-- Outer reduction retains epsilon's inner infinitesimal, not the identity. -/
theorem epsilonLiftSL_reduce (X : LieAlgebra.SpecialLinear.sl n R) :
    slReduce (DualNumber R) n (epsilonLiftSL X) = liftSL X := by
  apply Subtype.ext
  change ((liftMatrix X.1).map
    (algebraMap (DualNumber R) (DualNumber (DualNumber R)))).map
      (DualNumber.fstRingHom (DualNumber R)) = liftMatrix X.1
  apply Matrix.ext
  intro i j
  change ((algebraMap (DualNumber R) (DualNumber (DualNumber R)))
    (liftMatrix X.1 i j)).fst = liftMatrix X.1 i j
  rfl

/-- The eta factor lies in the native outer special-linear reduction kernel. -/
theorem etaLiftSL_reduce (Y : LieAlgebra.SpecialLinear.sl n R) :
    slReduce (DualNumber R) n (etaLiftSL Y) = 1 :=
  (slKerEquiv (Multiplicative.ofAdd (slMap (algebraMap R (DualNumber R)) Y))).property

/-- The ordered four-factor native special-linear commutator is the outer lift
of the pure-inner Lie bracket. -/
theorem epsilon_eta_SL_commutator (X Y : LieAlgebra.SpecialLinear.sl n R) :
    epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ =
      liftSL (innerPureSL (⁅X, Y⁆ : LieAlgebra.SpecialLinear.sl n R)) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  have h : Matrix.SpecialLinearGroup.toGL
      (liftSL (innerPureSL (⁅X, Y⁆ : LieAlgebra.SpecialLinear.sl n R))) =
      liftGL (innerPure (⁅X.1, Y.1⁆ : Matrix n n R)) := by
    apply Units.ext
    change liftMatrix (innerPure (⁅X, Y⁆ : LieAlgebra.SpecialLinear.sl n R).1) =
      liftMatrix (innerPure (⁅X.1, Y.1⁆ : Matrix n n R))
    rw [LieAlgebra.SpecialLinear.sl_bracket, LieRing.of_associative_ring_bracket]
  simpa only [map_mul, map_inv, epsilonLiftSL_toGL, etaLiftSL_toGL, h] using
    (epsilon_eta_commutator X.1 Y.1)

/-- The ordered commutator as an element of the actual native SL outer kernel. -/
def mixedSLKernel (X Y : LieAlgebra.SpecialLinear.sl n R) :
    (slReduce (DualNumber R) n).ker :=
  slKerEquiv (Multiplicative.ofAdd (innerPureSL ⁅X, Y⁆))

/-- The kernel element has the ordered native special-linear commutator as value. -/
@[simp] theorem mixedSLKernel_val (X Y : LieAlgebra.SpecialLinear.sl n R) :
    (mixedSLKernel X Y).1 =
      epsilonLiftSL X * etaLiftSL Y * (epsilonLiftSL X)⁻¹ * (etaLiftSL Y)⁻¹ :=
  (epsilon_eta_SL_commutator X Y).symm

/-- Native special-linear readback recovers the pure-inner Lie bracket. -/
@[simp] theorem mixedSLKernel_readback (X Y : LieAlgebra.SpecialLinear.sl n R) :
    slReadback (mixedSLKernel X Y) = innerPureSL ⁅X, Y⁆ :=
  slKerEquiv_readback _

/-- The outer-second, inner-second matrix entry is the ordered Lie bracket. -/
@[simp] theorem mixedSLKernel_snd_snd (X Y : LieAlgebra.SpecialLinear.sl n R) (i j : n) :
    (((mixedSLKernel X Y).1 : Matrix n n (DualNumber (DualNumber R))) i j).snd.snd =
      (⁅X, Y⁆ : LieAlgebra.SpecialLinear.sl n R).1 i j := by
  rw [← slReadback_apply, mixedSLKernel_readback]
  rfl

end Matrix.DualNumberMixedSLCommutator
