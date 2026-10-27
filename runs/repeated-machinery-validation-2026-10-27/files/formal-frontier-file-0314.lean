/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.DualNumberKernelAdjoint

/-!
# Mixed commutators in the native general linear group over iterated dual numbers

The ordered commutator of an inner infinitesimal lift and an outer infinitesimal lift
is the outer lift of the pure inner coefficient of the associative matrix Lie bracket.
-/

@[expose] public section
set_option warningAsError true

universe u v

namespace Matrix.DualNumberMixedCommutator

open Matrix.DualNumberKernels

variable {R : Type u} [CommRing R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The entrywise inner constant embedding of a coefficient matrix. -/
def innerConstant (Y : Matrix n n R) : Matrix n n (DualNumber R) :=
  Y.map (algebraMap R (DualNumber R))

/-- The inner pure-second matrix, embedded in the coefficients of the outer dual numbers. -/
def innerPure (X : Matrix n n R) : Matrix n n (DualNumber R) :=
  fun i j => (0, X i j)

/-- The inner infinitesimal native GL unit, embedded along outer constants. -/
def epsilonLiftGL (X : Matrix n n R) :
    Matrix.GeneralLinearGroup n (DualNumber (DualNumber R)) :=
  ⟨(liftMatrix X).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))),
    (liftMatrix (-X)).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))),
    by rw [← Matrix.map_mul, ← liftMatrix_add]
       simp,
    by rw [← Matrix.map_mul, ← liftMatrix_add]
       simp⟩

/-- The outer infinitesimal native GL unit with inner-constant coefficient matrix. -/
def etaLiftGL (Y : Matrix n n R) :
    Matrix.GeneralLinearGroup n (DualNumber (DualNumber R)) :=
  liftGL (innerConstant Y)

/-- Entrywise outer constant image of the inner unit `1 + εX`. -/
@[simp] theorem epsilonLiftGL_val (X : Matrix n n R) :
    (epsilonLiftGL X : Matrix n n (DualNumber (DualNumber R))) =
      (liftMatrix X).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))) := rfl

/-- The inner lift's native inverse is the outer constant image of `1 - εX`. -/
@[simp] theorem epsilonLiftGL_inv_val (X : Matrix n n R) :
    (((epsilonLiftGL X)⁻¹ : Matrix.GeneralLinearGroup n (DualNumber (DualNumber R))) :
      Matrix n n (DualNumber (DualNumber R))) =
      (liftMatrix (-X)).map (algebraMap (DualNumber R) (DualNumber (DualNumber R))) := rfl

/-- The outer lift has underlying matrix `1 + ηY` with inner-constant `Y`. -/
@[simp] theorem etaLiftGL_val (Y : Matrix n n R) :
    (etaLiftGL Y : Matrix n n (DualNumber (DualNumber R))) =
      liftMatrix (innerConstant Y) := rfl

/-- The outer lift has native inverse `1 - ηY`. -/
@[simp] theorem etaLiftGL_inv_val (Y : Matrix n n R) :
    (((etaLiftGL Y)⁻¹ : Matrix.GeneralLinearGroup n (DualNumber (DualNumber R))) :
      Matrix n n (DualNumber (DualNumber R))) =
      liftMatrix (-innerConstant Y) := rfl

omit [DecidableEq n] in
private theorem innerPure_mul_constant (X Y : Matrix n n R) :
    innerPure X * innerConstant Y = innerPure (X * Y) := by
  ext i j
  · simp only [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
    simp [innerPure, innerConstant, TrivSqZeroExt.algebraMap_eq_inlHom]
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, DualNumber.snd_mul]
    simp [innerPure, innerConstant, TrivSqZeroExt.algebraMap_eq_inlHom,
      Matrix.mul_apply]

omit [DecidableEq n] in
private theorem innerConstant_mul_pure (X Y : Matrix n n R) :
    innerConstant X * innerPure Y = innerPure (X * Y) := by
  ext i j
  · simp only [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
    simp [innerPure, innerConstant, TrivSqZeroExt.algebraMap_eq_inlHom]
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, DualNumber.snd_mul]
    simp [innerPure, innerConstant, TrivSqZeroExt.algebraMap_eq_inlHom,
      Matrix.mul_apply]

omit [DecidableEq n] in
private theorem innerPure_mul_pure (X Y : Matrix n n R) :
    innerPure X * innerPure Y = 0 := by
  ext i j
  · simp only [Matrix.mul_apply, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul]
    simp [innerPure]
  · simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, DualNumber.snd_mul]
    simp [innerPure]

omit [Fintype n] in
private theorem liftMatrix_eq_one_add_pure (X : Matrix n n R) :
    liftMatrix X = 1 + innerPure X := by
  ext i j
  · simp only [Matrix.add_apply, TrivSqZeroExt.fst_add, liftMatrix_fst]
    by_cases hij : i = j <;> simp [innerPure, Matrix.one_apply, hij]
  · simp only [Matrix.add_apply, TrivSqZeroExt.snd_add, liftMatrix_snd]
    by_cases hij : i = j <;> simp [innerPure, Matrix.one_apply, hij]

omit [Fintype n] [DecidableEq n] in
private theorem innerPure_sub (X Y : Matrix n n R) :
    innerPure (X - Y) = innerPure X - innerPure Y := by
  ext i j
  · simp only [Matrix.sub_apply, TrivSqZeroExt.fst_sub]
    simp [innerPure]
  · simp only [Matrix.sub_apply, TrivSqZeroExt.snd_sub]
    simp [innerPure]

private theorem inner_conj_difference (X Y : Matrix n n R) :
    ((liftGL X : Matrix.GeneralLinearGroup n (DualNumber R)) : Matrix n n (DualNumber R)) *
      innerConstant Y *
      (((liftGL X)⁻¹ : Matrix.GeneralLinearGroup n (DualNumber R)) :
        Matrix n n (DualNumber R)) - innerConstant Y = innerPure (X * Y - Y * X) := by
  have hzero : innerPure X * innerConstant Y * innerPure X = 0 := by
    rw [innerPure_mul_constant, innerPure_mul_pure]
  change liftMatrix X * innerConstant Y * liftMatrix (-X) - innerConstant Y = _
  rw [liftMatrix_eq_one_add_pure, liftMatrix_eq_one_add_pure]
  have hneg : innerPure (-X) = -innerPure X := by
    ext i j
    · simp only [Matrix.neg_apply, TrivSqZeroExt.fst_neg]
      simp [innerPure]
    · simp only [Matrix.neg_apply, TrivSqZeroExt.snd_neg]
      simp [innerPure]
  rw [hneg, innerPure_sub, ← innerPure_mul_constant X Y,
    ← innerConstant_mul_pure Y X]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, hzero]
  abel_nf

/-- Outer reduction remembers the inner infinitesimal conjugator, which need not be `1`. -/
theorem epsilon_reduce (X : Matrix n n R) :
    glReduce (DualNumber R) n (epsilonLiftGL X) = liftGL X := by
  apply Units.ext
  ext i j <;>
    simp [epsilonLiftGL, glReduce, liftMatrix, TrivSqZeroExt.algebraMap_eq_inlHom,
      TrivSqZeroExt.inlHom] <;> rfl

/-- The outer infinitesimal unit lies in the actual native GL reduction kernel. -/
theorem eta_reduce (Y : Matrix n n R) :
    glReduce (DualNumber R) n (etaLiftGL Y) = 1 :=
  (glKerEquiv (Multiplicative.ofAdd (innerConstant Y))).property

/-- The ordered native GL commutator is the full outer lift of the inner matrix Lie
bracket. Both inverse factors are the native unit inverses. -/
theorem epsilon_eta_commutator (X Y : Matrix n n R) :
    epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ =
      liftGL (innerPure (⁅X, Y⁆ : Matrix n n R)) := by
  let K : (glReduce (DualNumber R) n).ker :=
    glKerEquiv (Multiplicative.ofAdd (innerConstant Y))
  have hK : MulAut.conjNormal (epsilonLiftGL X) K * K⁻¹ =
      glKerEquiv (Multiplicative.ofAdd (innerPure (X * Y - Y * X))) := by
    dsimp [K]
    rw [glKerEquiv_conj, epsilon_reduce]
    change glKerEquiv (Multiplicative.ofAdd
        (((liftGL X : Matrix.GeneralLinearGroup n (DualNumber R)) :
          Matrix n n (DualNumber R)) * innerConstant Y *
          (((liftGL X)⁻¹ : Matrix.GeneralLinearGroup n (DualNumber R)) :
            Matrix n n (DualNumber R)))) *
      (glKerEquiv (Multiplicative.ofAdd (innerConstant Y)))⁻¹ = _
    rw [← map_inv, ← map_mul]
    simpa only [ofAdd_sub, div_eq_mul_inv] using
      congrArg (glKerEquiv (R := DualNumber R) (n := n))
        (congrArg Multiplicative.ofAdd (inner_conj_difference X Y))
  have hval := congrArg (fun k : (glReduce (DualNumber R) n).ker =>
    (k.1 : Matrix.GeneralLinearGroup n (DualNumber (DualNumber R)))) hK
  change epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ *
      (etaLiftGL Y)⁻¹ = liftGL (innerPure (X * Y - Y * X)) at hval
  simpa only [LieRing.of_associative_ring_bracket] using hval

/-- The mixed commutator as an element of the actual outer native reduction kernel. -/
def mixedKernel (X Y : Matrix n n R) : (glReduce (DualNumber R) n).ker :=
  glKerEquiv (Multiplicative.ofAdd (innerPure (⁅X, Y⁆ : Matrix n n R)))

/-- The kernel element has exactly the specified ordered native GL commutator as its unit. -/
@[simp] theorem mixedKernel_val (X Y : Matrix n n R) :
    (mixedKernel X Y).1 =
      epsilonLiftGL X * etaLiftGL Y * (epsilonLiftGL X)⁻¹ * (etaLiftGL Y)⁻¹ := by
  exact (epsilon_eta_commutator X Y).symm

/-- Readback in the outer native GL identity fiber retains the inner pure coefficient. -/
@[simp] theorem mixedKernel_readback (X Y : Matrix n n R) :
    glReadback (mixedKernel X Y) = innerPure (⁅X, Y⁆ : Matrix n n R) := by
  exact glKerEquiv_readback _

/-- The entire outer first coordinate is the identity matrix over inner dual numbers. -/
@[simp] theorem mixedKernel_fst (X Y : Matrix n n R) (i j : n) :
    (((mixedKernel X Y).1 : Matrix n n (DualNumber (DualNumber R))) i j).fst =
      (1 : Matrix n n (DualNumber R)) i j := by
  exact congrArg (fun A : Matrix n n (DualNumber R) => A i j)
    (glKernel_fst (mixedKernel X Y))

/-- The outer second coordinate has zero inner first coefficient. -/
@[simp] theorem mixedKernel_snd_fst (X Y : Matrix n n R) (i j : n) :
    (((mixedKernel X Y).1 : Matrix n n (DualNumber (DualNumber R))) i j).snd.fst =
      0 := by
  rw [← glReadback_apply, mixedKernel_readback]
  rfl

/-- The mixed coordinate is mathlib's existing associative matrix Lie bracket. -/
@[simp] theorem mixedKernel_snd_snd (X Y : Matrix n n R) (i j : n) :
    (((mixedKernel X Y).1 : Matrix n n (DualNumber (DualNumber R))) i j).snd.snd =
      (⁅X, Y⁆ : Matrix n n R) i j := by
  rw [← glReadback_apply, mixedKernel_readback]
  rfl

end Matrix.DualNumberMixedCommutator
