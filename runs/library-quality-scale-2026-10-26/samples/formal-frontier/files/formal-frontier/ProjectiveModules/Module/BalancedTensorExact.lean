/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import ProjectiveModules.Module.BalancedTensorProduct
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Exactness of balanced tensor products with a projective module

This file develops functorial maps for the balanced tensor product of a right
module and a left module over an arbitrary ring.  It then proves that fixing a
projective right module preserves short exact sequences in the left variable.
-/

@[expose] public section

universe uR uM uM' uM'' uN uN' uN'' uI uP uL

namespace BalancedTensorProduct

variable {R : Type uR} [Ring R]
variable {M : Type uM} {M' : Type uM'} {M'' : Type uM''}
variable {N : Type uN} {N' : Type uN'} {N'' : Type uN''}
variable [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
variable [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
variable [Module Rᵐᵒᵖ M] [Module Rᵐᵒᵖ M'] [Module Rᵐᵒᵖ M'']
variable [Module R N] [Module R N'] [Module R N'']

/-- The additive map on balanced tensor products induced by a right-linear map
in the first variable. -/
def mapLeft (f : M →ₗ[Rᵐᵒᵖ] M') :
    BalancedTensorProduct R M N →+ BalancedTensorProduct R M' N :=
  lift
    { toFun := fun m n ↦ f m ⊗ᵇ[R] n
      map_zero_left := fun n ↦ by simp
      map_add_left := fun m₁ m₂ n ↦ by simp [add_tmul]
      map_zero_right := fun m ↦ by simp
      map_add_right := fun m n₁ n₂ ↦ by simp [tmul_add]
      balance := fun r m n ↦ by rw [map_smul, smul_tmul] }

/-- The additive map on balanced tensor products induced by a left-linear map
in the second variable. -/
def mapRight (g : N →ₗ[R] N') :
    BalancedTensorProduct R M N →+ BalancedTensorProduct R M N' :=
  lift
    { toFun := fun m n ↦ m ⊗ᵇ[R] g n
      map_zero_left := fun n ↦ by simp
      map_add_left := fun m₁ m₂ n ↦ by simp [add_tmul]
      map_zero_right := fun m ↦ by simp
      map_add_right := fun m n₁ n₂ ↦ by simp [tmul_add]
      balance := fun r m n ↦ by rw [smul_tmul, map_smul] }

@[simp]
theorem mapLeft_tmul (f : M →ₗ[Rᵐᵒᵖ] M') (m : M) (n : N) :
    mapLeft (N := N) f (m ⊗ᵇ[R] n) = f m ⊗ᵇ[R] n :=
  lift_tmul _ _ _

@[simp]
theorem mapRight_tmul (g : N →ₗ[R] N') (m : M) (n : N) :
    mapRight (M := M) g (m ⊗ᵇ[R] n) = m ⊗ᵇ[R] g n :=
  lift_tmul _ _ _

@[simp]
theorem mapLeft_id :
    mapLeft (N := N) (LinearMap.id (R := Rᵐᵒᵖ) (M := M)) = AddMonoidHom.id _ := by
  apply hom_ext
  intro m n
  rfl

@[simp]
theorem mapRight_id :
    mapRight (M := M) (LinearMap.id (R := R) (M := N)) = AddMonoidHom.id _ := by
  apply hom_ext
  intro m n
  rfl

@[simp]
theorem mapLeft_comp (f : M →ₗ[Rᵐᵒᵖ] M') (g : M' →ₗ[Rᵐᵒᵖ] M'') :
    mapLeft (N := N) (g.comp f) =
      (mapLeft (N := N) g).comp (mapLeft (N := N) f) := by
  apply hom_ext
  intro m n
  rfl

@[simp]
theorem mapRight_comp (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') :
    mapRight (M := M) (g.comp f) =
      (mapRight (M := M) g).comp (mapRight (M := M) f) := by
  apply hom_ext
  intro m n
  rfl

@[simp]
theorem mapLeft_mapLeft (f : M →ₗ[Rᵐᵒᵖ] M') (g : M' →ₗ[Rᵐᵒᵖ] M'')
    (z : BalancedTensorProduct R M N) :
    mapLeft (N := N) g (mapLeft (N := N) f z) =
      mapLeft (N := N) (g.comp f) z := by
  exact DFunLike.congr_fun (mapLeft_comp f g).symm z

@[simp]
theorem mapRight_mapRight (f : N →ₗ[R] N') (g : N' →ₗ[R] N'')
    (z : BalancedTensorProduct R M N) :
    mapRight (M := M) g (mapRight (M := M) f z) =
      mapRight (M := M) (g.comp f) z := by
  exact DFunLike.congr_fun (mapRight_comp f g).symm z

theorem mapLeft_mapRight (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    (mapLeft (N := N') f).comp (mapRight (M := M) g) =
      (mapRight (M := M') g).comp (mapLeft (N := N) f) := by
  apply hom_ext
  intro m n
  rfl

theorem mapLeft_mapRight_apply (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N')
    (z : BalancedTensorProduct R M N) :
    mapLeft (N := N') f (mapRight (M := M) g z) =
      mapRight (M := M') g (mapLeft (N := N) f z) := by
  exact DFunLike.congr_fun (mapLeft_mapRight f g) z

@[simp]
theorem mapLeft_zero : mapLeft (N := N) (0 : M →ₗ[Rᵐᵒᵖ] M') = 0 := by
  apply hom_ext
  intro m n
  simp

@[simp]
theorem mapRight_zero : mapRight (M := M) (0 : N →ₗ[R] N') = 0 := by
  apply hom_ext
  intro m n
  simp

@[simp]
theorem mapLeft_add (f g : M →ₗ[Rᵐᵒᵖ] M') :
    mapLeft (N := N) (f + g) = mapLeft (N := N) f + mapLeft (N := N) g := by
  apply hom_ext
  intro m n
  simp [add_tmul]

@[simp]
theorem mapRight_add (f g : N →ₗ[R] N') :
    mapRight (M := M) (f + g) = mapRight (M := M) f + mapRight (M := M) g := by
  apply hom_ext
  intro m n
  simp [tmul_add]

section Free

variable {ι : Type uI}

/-- The coefficient map used to evaluate balanced tensors with a free first
factor. This is an implementation detail of `freeToFinsupp`. -/
noncomputable def freeCoefficient (i : ι) (n : N) : Rᵐᵒᵖ →+ (ι →₀ N) where
  toFun r := Finsupp.single i (MulOpposite.unop r • n)
  map_zero' := by simp
  map_add' r s := by simp [add_smul]

/-- The balanced map used by `freeToFinsupp`. -/
noncomputable def freeBalancedMap :
    BalancedMap (R := R) (M := ι →₀ Rᵐᵒᵖ) (N := N) (ι →₀ N) where
  toFun x n := Finsupp.liftAddHom (fun i ↦ freeCoefficient i n) x
  map_zero_left n := by simp
  map_add_left x y n := by simp
  map_zero_right x := by simp [freeCoefficient]
  map_add_right x n₁ n₂ := by simp [freeCoefficient, smul_add]
  balance r x n := by
    simp only [Finsupp.liftAddHom_apply]
    rw [Finsupp.sum_smul_index']
    · apply Finsupp.sum_congr
      intro i hi
      simp [freeCoefficient, mul_smul]
    · intro i
      simp [freeCoefficient]

/-- A balanced tensor with a free right module, evaluated coordinatewise. -/
noncomputable def freeToFinsupp :
    BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N →+ (ι →₀ N) :=
  lift freeBalancedMap

@[simp]
theorem freeToFinsupp_tmul (x : ι →₀ Rᵐᵒᵖ) (n : N) :
    freeToFinsupp (R := R) (N := N) (x ⊗ᵇ[R] n) =
      Finsupp.liftAddHom (fun i ↦ freeCoefficient i n) x :=
  lift_tmul _ _ _

@[simp]
theorem freeToFinsupp_single_tmul (i : ι) (r : Rᵐᵒᵖ) (n : N) :
    freeToFinsupp (R := R) (N := N) (Finsupp.single i r ⊗ᵇ[R] n) =
      Finsupp.single i (MulOpposite.unop r • n) := by
  simp [freeToFinsupp_tmul, freeCoefficient]

/-- The single-coordinate map used by `finsuppToFree`. -/
noncomputable def freeSingle (i : ι) :
    N →+ BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N where
  toFun n := Finsupp.single i (1 : Rᵐᵒᵖ) ⊗ᵇ[R] n
  map_zero' := by simp
  map_add' n₁ n₂ := by simp [tmul_add]

/-- Reassemble a finitely supported family as a sum of elementary balanced
tensors. -/
noncomputable def finsuppToFree :
    (ι →₀ N) →+ BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N :=
  Finsupp.liftAddHom freeSingle

@[simp]
theorem finsuppToFree_single (i : ι) (n : N) :
    finsuppToFree (R := R) (Finsupp.single i n) =
      Finsupp.single i (1 : Rᵐᵒᵖ) ⊗ᵇ[R] n := by
  simp [finsuppToFree, freeSingle]

private theorem finsuppToFree_freeToFinsupp_tmul
    (x : ι →₀ Rᵐᵒᵖ) (n : N) :
    finsuppToFree (R := R) (freeToFinsupp (R := R) (N := N) (x ⊗ᵇ[R] n)) =
      x ⊗ᵇ[R] n := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add i r x hir hr ih =>
      rw [add_tmul, map_add, map_add, ih]
      congr 1
      rw [freeToFinsupp_single_tmul, finsuppToFree_single,
        ← smul_tmul (MulOpposite.unop r)]
      simp

/-- A balanced tensor with a free right module is the finitely supported
family of its coordinates. -/
noncomputable def freeAddEquiv :
    BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N ≃+ (ι →₀ N) where
  toFun := freeToFinsupp
  invFun := finsuppToFree
  map_add' := map_add _
  left_inv z := by
    induction z using induction_on with
    | zero => simp
    | pure x n => exact finsuppToFree_freeToFinsupp_tmul x n
    | neg z hz => simpa using congrArg Neg.neg hz
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  right_inv x := by
    induction x using Finsupp.induction with
    | zero => simp
    | single_add i n x hin hn ih =>
        rw [map_add, map_add, finsuppToFree_single, freeToFinsupp_single_tmul, ih]
        simp

@[simp]
theorem freeAddEquiv_tmul (x : ι →₀ Rᵐᵒᵖ) (n : N) :
    freeAddEquiv (R := R) (N := N) (x ⊗ᵇ[R] n) =
      Finsupp.liftAddHom (fun i ↦ freeCoefficient i n) x :=
  freeToFinsupp_tmul x n

@[simp]
theorem freeAddEquiv_symm_single (i : ι) (n : N) :
    (freeAddEquiv (R := R) (N := N)).symm (Finsupp.single i n) =
      Finsupp.single i (1 : Rᵐᵒᵖ) ⊗ᵇ[R] n :=
  finsuppToFree_single i n

theorem freeAddEquiv_mapRight (g : N →ₗ[R] N')
    (z : BalancedTensorProduct R (ι →₀ Rᵐᵒᵖ) N) :
    freeAddEquiv (R := R) (N := N') (mapRight g z) =
      Finsupp.mapRange.linearMap g (freeAddEquiv (R := R) (N := N) z) := by
  induction z using induction_on with
  | zero => simp
  | pure x n =>
      induction x using Finsupp.induction with
      | zero => simp
      | single_add i r x hir hr ih =>
          have hsingle :
              freeAddEquiv (R := R) (N := N')
                  (mapRight g (Finsupp.single i r ⊗ᵇ[R] n)) =
                Finsupp.mapRange.linearMap g
                  (freeAddEquiv (R := R) (N := N) (Finsupp.single i r ⊗ᵇ[R] n)) := by
            simp [mapRight_tmul, freeAddEquiv_tmul, freeCoefficient]
          simpa only [add_tmul, map_add] using congrArg₂ (· + ·) hsingle ih
  | neg z hz => simpa only [map_neg] using congrArg Neg.neg hz
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensoring a free right module with an injective map in the second variable
is injective. -/
theorem mapRight_injective_free (g : N →ₗ[R] N') (hg : Function.Injective g) :
    Function.Injective (mapRight (M := ι →₀ Rᵐᵒᵖ) g) := by
  intro x y hxy
  apply (freeAddEquiv (R := R) (N := N)).injective
  apply Finsupp.mapRange_injective g (map_zero g) hg
  have he := congrArg (freeAddEquiv (R := R) (N := N')) hxy
  rw [freeAddEquiv_mapRight, freeAddEquiv_mapRight] at he
  exact he

/-- Tensoring a free right module preserves an exact pair in the second
variable when the first map is injective. -/
theorem exact_mapRight_free (i : N →ₗ[R] N') (p : N' →ₗ[R] N'')
    (hi : Function.Injective i) (h : Function.Exact i p) :
    Function.Exact (mapRight (M := ι →₀ Rᵐᵒᵖ) i)
      (mapRight (M := ι →₀ Rᵐᵒᵖ) p) := by
  let fi := Finsupp.mapRange.linearMap (α := ι) i
  let fp := Finsupp.mapRange.linearMap (α := ι) p
  have hfi : Function.Exact fi fp := by
    rw [LinearMap.exact_iff, Finsupp.ker_mapRange,
      Finsupp.range_mapRange_linearMap i (LinearMap.ker_eq_bot.mpr hi) ι,
      h.linearMap_ker_eq]
  intro x
  constructor
  · intro hx
    have hx' : fp (freeAddEquiv (R := R) (N := N') x) = 0 := by
      have he := congrArg (freeAddEquiv (R := R) (N := N'')) hx
      rw [freeAddEquiv_mapRight, map_zero] at he
      exact he
    obtain ⟨y, hy⟩ := (hfi _).mp hx'
    refine ⟨(freeAddEquiv (R := R) (N := N)).symm y, ?_⟩
    apply (freeAddEquiv (R := R) (N := N')).injective
    rw [freeAddEquiv_mapRight, AddEquiv.apply_symm_apply]
    change fi y = freeAddEquiv (R := R) (N := N') x
    exact hy
  · rintro ⟨y, rfl⟩
    have hy := (hfi (fi (freeAddEquiv (R := R) (N := N) y))).mpr
      ⟨freeAddEquiv (R := R) (N := N) y, rfl⟩
    change mapRight p (mapRight i y) = 0
    apply (freeAddEquiv (R := R) (N := N'')).injective
    rw [freeAddEquiv_mapRight, freeAddEquiv_mapRight]
    exact hy

end Free

/-- A surjective map in the second variable induces a surjective map of
balanced tensor products. -/
theorem mapRight_surjective (g : N →ₗ[R] N') (hg : Function.Surjective g) :
    Function.Surjective (mapRight (M := M) g) := by
  intro z
  induction z using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | pure m n =>
      obtain ⟨n', rfl⟩ := hg n
      exact ⟨m ⊗ᵇ[R] n', mapRight_tmul _ _ _⟩
  | neg z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact ⟨-y, map_neg _ _⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

end BalancedTensorProduct

namespace Module.Projective

variable {R : Type uR} [Ring R]
variable {P : Type uP} {L : Type uL} {M : Type uM} {N : Type uN}
variable [AddCommGroup P] [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
variable [Module Rᵐᵒᵖ P] [Module R L] [Module R M] [Module R N]

/-- Tensoring with a projective right module preserves injective maps in the
left-module variable. -/
theorem balancedTensor_injective [Module.Projective Rᵐᵒᵖ P]
    (i : L →ₗ[R] M) (hi : Function.Injective i) :
    Function.Injective (BalancedTensorProduct.mapRight (M := P) i) := by
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := Rᵐᵒᵖ) (P := P)).mp inferInstance
  let q : (P →₀ Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] P := Finsupp.linearCombination Rᵐᵒᵖ id
  intro x y hxy
  have hxy' := congrArg (BalancedTensorProduct.mapLeft (N := M) s) hxy
  rw [BalancedTensorProduct.mapLeft_mapRight_apply,
    BalancedTensorProduct.mapLeft_mapRight_apply] at hxy'
  have hfree := BalancedTensorProduct.mapRight_injective_free
    (ι := P) i hi hxy'
  have hback := congrArg (BalancedTensorProduct.mapLeft (N := L) q) hfree
  simpa [BalancedTensorProduct.mapLeft_mapLeft, q, hs] using hback

/-- Tensoring with a projective right module preserves an exact pair in the
left-module variable when the first map is injective. -/
theorem balancedTensor_exact [Module.Projective Rᵐᵒᵖ P]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (hi : Function.Injective i) (h : Function.Exact i p) :
    Function.Exact (BalancedTensorProduct.mapRight (M := P) i)
      (BalancedTensorProduct.mapRight (M := P) p) := by
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := Rᵐᵒᵖ) (P := P)).mp inferInstance
  let q : (P →₀ Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] P := Finsupp.linearCombination Rᵐᵒᵖ id
  have hfree := BalancedTensorProduct.exact_mapRight_free (ι := P) i p hi h
  intro x
  constructor
  · intro hx
    have hx' : BalancedTensorProduct.mapRight (M := P →₀ Rᵐᵒᵖ) p
        (BalancedTensorProduct.mapLeft (N := M) s x) = 0 := by
      rw [← BalancedTensorProduct.mapLeft_mapRight_apply, hx, map_zero]
    obtain ⟨y, hy⟩ := (hfree _).mp hx'
    refine ⟨BalancedTensorProduct.mapLeft (N := L) q y, ?_⟩
    rw [← BalancedTensorProduct.mapLeft_mapRight_apply, hy,
      BalancedTensorProduct.mapLeft_mapLeft]
    simp [q, hs]
  · rintro ⟨y, rfl⟩
    rw [BalancedTensorProduct.mapRight_mapRight, h.linearMap_comp_eq_zero,
      BalancedTensorProduct.mapRight_zero]
    rfl

/-- Applying balanced tensor with a projective right module to an
injective/exact/surjective pair preserves all three properties. -/
theorem balancedTensor_short_exact [Module.Projective Rᵐᵒᵖ P]
    (i : L →ₗ[R] M) (p : M →ₗ[R] N)
    (hi : Function.Injective i) (h : Function.Exact i p)
    (hp : Function.Surjective p) :
    Function.Injective (BalancedTensorProduct.mapRight (M := P) i) ∧
      Function.Exact (BalancedTensorProduct.mapRight (M := P) i)
        (BalancedTensorProduct.mapRight (M := P) p) ∧
      Function.Surjective (BalancedTensorProduct.mapRight (M := P) p) :=
  ⟨balancedTensor_injective i hi, balancedTensor_exact i p hi h,
    BalancedTensorProduct.mapRight_surjective p hp⟩

end Module.Projective
