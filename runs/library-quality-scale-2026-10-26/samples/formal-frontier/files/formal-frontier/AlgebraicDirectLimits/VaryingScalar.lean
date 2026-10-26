/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Directed limits with varying scalars

This file equips the concrete directed limit of a compatible system of modules
with its canonical action by the directed limit of the scalar semirings. It then
identifies the tensor product of two such module limits with the directed limit
of the stagewise tensor products.

No transition map is required to be injective.
-/

@[expose] public section

universe u v w x

open DirectLimit

namespace DirectLimit.VaryingScalar

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable (A : ι → Type v) [∀ i, CommSemiring (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)
variable [DirectedSystem A (f · · ·)]
variable (M : ι → Type w) [∀ i, AddCommMonoid (M i)] [∀ i, Module (A i) (M i)]
variable (g : ∀ i j (h : i ≤ j), M i →ₛₗ[f i j h] M j)
variable [DirectedSystem M (g · · ·)]

/-- The concrete directed limit of the varying scalar semirings. -/
abbrev ScalarLimit := DirectLimit A (f · · ·)

/-- The representative-level action of the scalar-semiring limit on the module limit. -/
noncomputable def smulDef : ScalarLimit A f →
    DirectLimit M (fun i j h ↦ g i j h) →
      DirectLimit M (fun i j h ↦ g i j h) :=
  DirectLimit.map₂ (f · · ·) (g · · ·) (g · · ·) (fun _ a m ↦ a • m) (by
    intro i j hij a m
    exact (g i j hij).map_smulₛₗ a m)

omit [Nonempty ι] in
@[simp] theorem smulDef_mk (i : ι) (a : A i) (m : M i) :
    smulDef A f M g (⟦⟨i, a⟩⟧ : ScalarLimit A f)
        (⟦⟨i, m⟩⟧ : DirectLimit M (fun i j h ↦ g i j h)) =
      (⟦⟨i, a • m⟩⟧ : DirectLimit M (fun i j h ↦ g i j h)) :=
  DirectLimit.map₂_def _ _ _ _ _ _ _ _

noncomputable instance instModule :
    Module (ScalarLimit A f) (DirectLimit M (fun i j h ↦ g i j h)) where
  smul := smulDef A f M g
  one_smul x := by
    change smulDef A f M g 1 x = x
    induction x using DirectLimit.induction with
    | _ i x => rw [DirectLimit.one_def i, smulDef_mk, one_smul]
  mul_smul a b x := by
    change smulDef A f M g (a * b) x =
      smulDef A f M g a (smulDef A f M g b x)
    induction a, b using DirectLimit.induction₂ with
    | _ i a b =>
      induction x using DirectLimit.induction with
      | _ j x =>
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        rw [DirectLimit.eq_of_le ⟨i, a⟩ k hik,
          DirectLimit.eq_of_le ⟨i, b⟩ k hik,
          DirectLimit.eq_of_le ⟨j, x⟩ k hjk,
          DirectLimit.mul_def, smulDef_mk, smulDef_mk, smulDef_mk, mul_smul]
  smul_zero a := by
    change smulDef A f M g a 0 = 0
    induction a using DirectLimit.induction with
    | _ i a => rw [DirectLimit.zero_def i, smulDef_mk, smul_zero]
  smul_add a x y := by
    change smulDef A f M g a (x + y) =
      smulDef A f M g a x + smulDef A f M g a y
    induction a using DirectLimit.induction with
    | _ i a =>
      induction x, y using DirectLimit.induction₂ with
      | _ j x y =>
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        rw [DirectLimit.eq_of_le ⟨i, a⟩ k hik,
          DirectLimit.eq_of_le ⟨j, x⟩ k hjk,
          DirectLimit.eq_of_le ⟨j, y⟩ k hjk,
          DirectLimit.add_def, smulDef_mk, smulDef_mk, smulDef_mk, smul_add,
          ← DirectLimit.add_def]
  add_smul a b x := by
    change smulDef A f M g (a + b) x =
      smulDef A f M g a x + smulDef A f M g b x
    induction a, b using DirectLimit.induction₂ with
    | _ i a b =>
      induction x using DirectLimit.induction with
      | _ j x =>
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        rw [DirectLimit.eq_of_le ⟨i, a⟩ k hik,
          DirectLimit.eq_of_le ⟨i, b⟩ k hik,
          DirectLimit.eq_of_le ⟨j, x⟩ k hjk,
          DirectLimit.add_def, smulDef_mk, smulDef_mk, smulDef_mk, add_smul,
          ← DirectLimit.add_def]
  zero_smul x := by
    change smulDef A f M g 0 x = 0
    induction x using DirectLimit.induction with
    | _ i x => rw [DirectLimit.zero_def i, smulDef_mk, zero_smul,
        ← DirectLimit.zero_def i]

@[simp]
theorem smul_mk (i : ι) (a : A i) (m : M i) :
    (⟦⟨i, a⟩⟧ : ScalarLimit A f) •
        (⟦⟨i, m⟩⟧ : DirectLimit M (fun i j h ↦ g i j h)) =
      (⟦⟨i, a • m⟩⟧ : DirectLimit M (fun i j h ↦ g i j h)) :=
  smulDef_mk A f M g i a m

/-- The canonical semilinear map from a stage module to its varying-scalar limit. -/
def of (i : ι) : M i →ₛₗ[DirectLimit.Ring.of A (f · · ·) i]
    DirectLimit M (fun i j h ↦ g i j h) where
  toFun m := ⟦⟨i, m⟩⟧
  map_add' _ _ := (DirectLimit.add_def ..).symm
  map_smul' a m := (smul_mk A f M g i a m).symm

@[simp]
theorem of_apply (i : ι) (m : M i) : of A f M g i m = ⟦⟨i, m⟩⟧ := rfl

theorem of_map {i j : ι} (hij : i ≤ j) (m : M i) :
    of A f M g j (g i j hij m) = of A f M g i m :=
  (DirectLimit.eq_of_le ⟨i, m⟩ j hij).symm

section TensorProduct

variable (N : ι → Type x) [∀ i, AddCommMonoid (N i)] [∀ i, Module (A i) (N i)]
variable (h : ∀ i j (hij : i ≤ j), N i →ₛₗ[f i j hij] N j)
variable [DirectedSystem N (h · · ·)]

/-- The transition map on tensor products induced by two semilinear systems. -/
def tensorMap (i j : ι) (hij : i ≤ j) :
    TensorProduct (A i) (M i) (N i) →ₛₗ[f i j hij]
      TensorProduct (A j) (M j) (N j) :=
  TensorProduct.map (g i j hij) (h i j hij)

instance instDirectedSystemTensorProduct :
    DirectedSystem (fun i ↦ TensorProduct (A i) (M i) (N i))
      (tensorMap A f M g N h · · ·) where
  map_self i x := by
    refine TensorProduct.inductionOn x (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [tensorMap, TensorProduct.map_tmul, DirectedSystem.map_self']
    · simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_map _ _ _ hij hjk x := by
    refine TensorProduct.inductionOn x (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [tensorMap, TensorProduct.map_tmul, DirectedSystem.map_map']
    · simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The canonical additive map from a stage tensor product to its direct limit. -/
def tensorOf (i : ι) : TensorProduct (A i) (M i) (N i) →+
    DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
      (tensorMap A f M g N h · · ·) where
  toFun x := ⟦⟨i, x⟩⟧
  map_zero' := (DirectLimit.zero_def i).symm
  map_add' _ _ := (DirectLimit.add_def ..).symm

omit [DirectedSystem A (f · · ·)] in
@[simp] theorem tensorOf_apply (i : ι) (x : TensorProduct (A i) (M i) (N i)) :
    tensorOf A f M g N h i x = ⟦⟨i, x⟩⟧ := rfl

omit [DirectedSystem A (f · · ·)] in
theorem tensorOf_map {i j : ι} (hij : i ≤ j)
    (x : TensorProduct (A i) (M i) (N i)) :
    tensorOf A f M g N h j (tensorMap A f M g N h i j hij x) =
      tensorOf A f M g N h i x := by
  change (⟦⟨j, tensorMap A f M g N h i j hij x⟩⟧ :
      DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
        (fun i j hij ↦ tensorMap A f M g N h i j hij)) =
    (⟦⟨i, x⟩⟧ : DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
      (fun i j hij ↦ tensorMap A f M g N h i j hij))
  exact (DirectLimit.eq_of_le
    (f := fun i j hij ↦ tensorMap A f M g N h i j hij) ⟨i, x⟩ j hij).symm

/-- Pair two module-limit representatives in the direct limit of stage tensor products. -/
noncomputable def pairing :
    DirectLimit M (fun i j hij ↦ g i j hij) →
      DirectLimit N (fun i j hij ↦ h i j hij) →
        DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
          (tensorMap A f M g N h · · ·) :=
  DirectLimit.lift₂ (g · · ·) (h · · ·)
    (fun i m n ↦ tensorOf A f M g N h i (m ⊗ₜ n)) (by
      intro i j hij m n
      exact (tensorOf_map A f M g N h hij (m ⊗ₜ n)).symm)

omit [DirectedSystem A (f · · ·)] in
@[simp] theorem pairing_mk (i : ι) (m : M i) (n : N i) :
    pairing A f M g N h ⟦⟨i, m⟩⟧ ⟦⟨i, n⟩⟧ =
      tensorOf A f M g N h i (m ⊗ₜ n) :=
  DirectLimit.lift₂_def _ _ _ _ _ _ _

omit [DirectedSystem A (f · · ·)] in
theorem pairing_add_left
    (m₁ m₂ : DirectLimit M (fun i j hij ↦ g i j hij))
    (n : DirectLimit N (fun i j hij ↦ h i j hij)) :
    pairing A f M g N h (m₁ + m₂) n =
      pairing A f M g N h m₁ n + pairing A f M g N h m₂ n := by
  induction m₁, m₂ using DirectLimit.induction₂ with
  | _ i m₁ m₂ =>
    induction n using DirectLimit.induction with
    | _ j n =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      rw [DirectLimit.eq_of_le ⟨i, m₁⟩ k hik,
        DirectLimit.eq_of_le ⟨i, m₂⟩ k hik,
        DirectLimit.eq_of_le ⟨j, n⟩ k hjk,
        DirectLimit.add_def, pairing_mk, pairing_mk, pairing_mk,
        TensorProduct.add_tmul, map_add]

omit [DirectedSystem A (f · · ·)] in
theorem pairing_add_right
    (m : DirectLimit M (fun i j hij ↦ g i j hij))
    (n₁ n₂ : DirectLimit N (fun i j hij ↦ h i j hij)) :
    pairing A f M g N h m (n₁ + n₂) =
      pairing A f M g N h m n₁ + pairing A f M g N h m n₂ := by
  induction m using DirectLimit.induction with
  | _ i m =>
    induction n₁, n₂ using DirectLimit.induction₂ with
    | _ j n₁ n₂ =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      rw [DirectLimit.eq_of_le ⟨i, m⟩ k hik,
        DirectLimit.eq_of_le ⟨j, n₁⟩ k hjk,
        DirectLimit.eq_of_le ⟨j, n₂⟩ k hjk,
        DirectLimit.add_def, pairing_mk, pairing_mk, pairing_mk,
        TensorProduct.tmul_add, map_add]

theorem pairing_smul_left
    (a : ScalarLimit A f)
    (m : DirectLimit M (fun i j hij ↦ g i j hij))
    (n : DirectLimit N (fun i j hij ↦ h i j hij)) :
    pairing A f M g N h (a • m) n =
      a • pairing A f M g N h m n := by
  induction a using DirectLimit.induction with
  | _ i a =>
    induction m using DirectLimit.induction with
    | _ j m =>
      induction n using DirectLimit.induction with
      | _ l n =>
        obtain ⟨k, hik, hjk, hlk⟩ := directed_of₃ (· ≤ ·) i j l
        rw [DirectLimit.eq_of_le ⟨i, a⟩ k hik,
          DirectLimit.eq_of_le ⟨j, m⟩ k hjk,
          DirectLimit.eq_of_le ⟨l, n⟩ k hlk,
          smul_mk, pairing_mk, pairing_mk, tensorOf_apply, tensorOf_apply, smul_mk,
          ← TensorProduct.smul_tmul']

theorem pairing_smul_right
    (a : ScalarLimit A f)
    (m : DirectLimit M (fun i j hij ↦ g i j hij))
    (n : DirectLimit N (fun i j hij ↦ h i j hij)) :
    pairing A f M g N h m (a • n) =
      a • pairing A f M g N h m n := by
  induction a using DirectLimit.induction with
  | _ i a =>
    induction m using DirectLimit.induction with
    | _ j m =>
      induction n using DirectLimit.induction with
      | _ l n =>
        obtain ⟨k, hik, hjk, hlk⟩ := directed_of₃ (· ≤ ·) i j l
        rw [DirectLimit.eq_of_le ⟨i, a⟩ k hik,
          DirectLimit.eq_of_le ⟨j, m⟩ k hjk,
          DirectLimit.eq_of_le ⟨l, n⟩ k hlk,
          smul_mk, pairing_mk, pairing_mk, tensorOf_apply, tensorOf_apply, smul_mk,
          TensorProduct.tmul_smul]

/-- The bilinear pairing on the two varying-scalar direct limits. -/
noncomputable def pairingLinear :
    DirectLimit M (fun i j hij ↦ g i j hij) →ₗ[ScalarLimit A f]
      DirectLimit N (fun i j hij ↦ h i j hij) →ₗ[ScalarLimit A f]
        DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
          (tensorMap A f M g N h · · ·) where
  toFun m :=
    { toFun := pairing A f M g N h m
      map_add' := pairing_add_right A f M g N h m
      map_smul' := fun a n ↦ by
        simpa using pairing_smul_right A f M g N h a m n }
  map_add' m₁ m₂ := by
    ext n
    exact pairing_add_left A f M g N h m₁ m₂ n
  map_smul' a m := by
    ext n
    exact pairing_smul_left A f M g N h a m n

/-- The map from the tensor product of the two limits to the limit of stage tensor products. -/
noncomputable def toTensorLimit :
    TensorProduct (ScalarLimit A f)
        (DirectLimit M (fun i j hij ↦ g i j hij))
        (DirectLimit N (fun i j hij ↦ h i j hij)) →ₗ[ScalarLimit A f]
      DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
        (tensorMap A f M g N h · · ·) :=
  TensorProduct.lift (pairingLinear A f M g N h)

theorem toTensorLimit_tmul_mk (i : ι) (m : M i) (n : N i) :
    toTensorLimit A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) := by
  rw [toTensorLimit, TensorProduct.lift.tmul]
  change pairing A f M g N h ⟦⟨i, m⟩⟧ ⟦⟨i, n⟩⟧ = _
  exact pairing_mk A f M g N h i m n

/-- The tensor-limit map on quotient representatives, its simp normal form. -/
@[simp]
theorem toTensorLimit_tmul_mk_mk (i : ι) (m : M i) (n : N i) :
    toTensorLimit A f M g N h (⟦⟨i, m⟩⟧ ⊗ₜ[ScalarLimit A f] ⟦⟨i, n⟩⟧) =
      ⟦⟨i, m ⊗ₜ[A i] n⟩⟧ :=
  toTensorLimit_tmul_mk A f M g N h i m n

/-- Map a stage tensor product into the tensor product of the two limits. -/
noncomputable def tensorToLimits (i : ι) :
    TensorProduct (A i) (M i) (N i) →ₛₗ[DirectLimit.Ring.of A (f · · ·) i]
      TensorProduct (ScalarLimit A f)
        (DirectLimit M (fun i j hij ↦ g i j hij))
        (DirectLimit N (fun i j hij ↦ h i j hij)) :=
  TensorProduct.map (of A f M g i) (of A f N h i)

@[simp]
theorem tensorToLimits_tmul (i : ι) (m : M i) (n : N i) :
    tensorToLimits A f M g N h i (m ⊗ₜ[A i] n) =
      of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n :=
  TensorProduct.map_tmul (of A f M g i) (of A f N h i) m n

theorem tensorToLimits_map {i j : ι} (hij : i ≤ j)
    (x : TensorProduct (A i) (M i) (N i)) :
    tensorToLimits A f M g N h j (tensorMap A f M g N h i j hij x) =
      tensorToLimits A f M g N h i x := by
  refine TensorProduct.inductionOn x (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
  · simp only [tensorMap, TensorProduct.map_tmul, tensorToLimits_tmul,
      of_map A f M g hij, of_map A f N h hij]
  · simpa only [map_add] using congrArg₂ (fun x y ↦ x + y) hx hy

/-- The representative-level map from the limit of stage tensor products back to the
tensor product of the limits. -/
noncomputable def fromTensorLimitDef :
    DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
        (tensorMap A f M g N h · · ·) →
      TensorProduct (ScalarLimit A f)
        (DirectLimit M (fun i j hij ↦ g i j hij))
        (DirectLimit N (fun i j hij ↦ h i j hij)) :=
  DirectLimit.lift (tensorMap A f M g N h · · ·)
    (fun i ↦ tensorToLimits A f M g N h i)
    (fun _ _ hij x ↦ (tensorToLimits_map A f M g N h hij x).symm)

@[simp]
theorem fromTensorLimitDef_mk (i : ι) (x : TensorProduct (A i) (M i) (N i)) :
    fromTensorLimitDef A f M g N h ⟦⟨i, x⟩⟧ = tensorToLimits A f M g N h i x :=
  rfl

theorem fromTensorLimitDef_add
    (x y : DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
      (tensorMap A f M g N h · · ·)) :
    fromTensorLimitDef A f M g N h (x + y) =
      fromTensorLimitDef A f M g N h x + fromTensorLimitDef A f M g N h y := by
  induction x, y using DirectLimit.induction₂ with
  | _ i x y =>
    rw [DirectLimit.add_def, fromTensorLimitDef_mk, fromTensorLimitDef_mk,
      fromTensorLimitDef_mk, map_add]

theorem fromTensorLimitDef_smul
    (a : ScalarLimit A f)
    (x : DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
      (tensorMap A f M g N h · · ·)) :
    fromTensorLimitDef A f M g N h (a • x) =
      a • fromTensorLimitDef A f M g N h x := by
  induction a using DirectLimit.induction with
  | _ i a =>
    induction x using DirectLimit.induction with
    | _ j x =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      rw [DirectLimit.eq_of_le (f := fun i j hij ↦ f i j hij) ⟨i, a⟩ k hik,
        DirectLimit.eq_of_le
          (f := fun i j hij ↦ tensorMap A f M g N h i j hij) ⟨j, x⟩ k hjk,
        smul_mk, fromTensorLimitDef_mk, fromTensorLimitDef_mk]
      exact (tensorToLimits A f M g N h k).map_smulₛₗ _ _

/-- The map from the limit of stage tensor products to the tensor product of the limits. -/
noncomputable def fromTensorLimit :
    DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
        (tensorMap A f M g N h · · ·) →ₗ[ScalarLimit A f]
      TensorProduct (ScalarLimit A f)
        (DirectLimit M (fun i j hij ↦ g i j hij))
        (DirectLimit N (fun i j hij ↦ h i j hij)) where
  toFun := fromTensorLimitDef A f M g N h
  map_add' := fromTensorLimitDef_add A f M g N h
  map_smul' := fromTensorLimitDef_smul A f M g N h

@[simp]
theorem fromTensorLimit_mk (i : ι) (x : TensorProduct (A i) (M i) (N i)) :
    fromTensorLimit A f M g N h ⟦⟨i, x⟩⟧ = tensorToLimits A f M g N h i x :=
  rfl

theorem fromTensorLimit_toTensorLimit
    (x : TensorProduct (ScalarLimit A f)
      (DirectLimit M (fun i j hij ↦ g i j hij))
      (DirectLimit N (fun i j hij ↦ h i j hij))) :
    fromTensorLimit A f M g N h (toTensorLimit A f M g N h x) = x := by
  refine TensorProduct.inductionOn x (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
  · induction m using DirectLimit.induction with
    | _ i m =>
      induction n using DirectLimit.induction with
      | _ j n =>
        obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
        rw [DirectLimit.eq_of_le (f := fun i j hij ↦ g i j hij) ⟨i, m⟩ k hik,
          DirectLimit.eq_of_le (f := fun i j hij ↦ h i j hij) ⟨j, n⟩ k hjk]
        change fromTensorLimit A f M g N h
          (toTensorLimit A f M g N h
            (of A f M g k (g i k hik m) ⊗ₜ[ScalarLimit A f]
              of A f N h k (h j k hjk n))) = _
        rw [toTensorLimit_tmul_mk, tensorOf_apply, fromTensorLimit_mk,
          tensorToLimits_tmul]
        rfl
  · rw [map_add, map_add, hx, hy]

theorem toTensorLimit_fromTensorLimit
    (x : DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
      (tensorMap A f M g N h · · ·)) :
    toTensorLimit A f M g N h (fromTensorLimit A f M g N h x) = x := by
  induction x using DirectLimit.induction with
  | _ i x =>
    rw [fromTensorLimit_mk]
    refine TensorProduct.inductionOn x (fun m n ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [tensorToLimits_tmul, toTensorLimit_tmul_mk, tensorOf_apply]
    · rw [map_add, map_add, hx, hy, DirectLimit.add_def]

/-- Tensor products commute with directed limits even when the scalar semiring varies along the
same directed system. -/
noncomputable def tensorProductEquiv :
    TensorProduct (ScalarLimit A f)
        (DirectLimit M (fun i j hij ↦ g i j hij))
        (DirectLimit N (fun i j hij ↦ h i j hij)) ≃ₗ[ScalarLimit A f]
      DirectLimit (fun i ↦ TensorProduct (A i) (M i) (N i))
        (tensorMap A f M g N h · · ·) :=
  LinearEquiv.ofLinearMap (toTensorLimit A f M g N h)
    (fromTensorLimit A f M g N h)
    (LinearMap.ext fun x ↦ toTensorLimit_fromTensorLimit A f M g N h x)
    (LinearMap.ext fun x ↦ fromTensorLimit_toTensorLimit A f M g N h x)

theorem tensorProductEquiv_tmul_mk (i : ι) (m : M i) (n : N i) :
    tensorProductEquiv A f M g N h
        (of A f M g i m ⊗ₜ[ScalarLimit A f] of A f N h i n) =
      tensorOf A f M g N h i (m ⊗ₜ[A i] n) :=
  toTensorLimit_tmul_mk A f M g N h i m n

/-- The tensor equivalence on quotient representatives, its simp normal form. -/
@[simp]
theorem tensorProductEquiv_tmul_mk_mk (i : ι) (m : M i) (n : N i) :
    tensorProductEquiv A f M g N h (⟦⟨i, m⟩⟧ ⊗ₜ[ScalarLimit A f] ⟦⟨i, n⟩⟧) =
      ⟦⟨i, m ⊗ₜ[A i] n⟩⟧ :=
  tensorProductEquiv_tmul_mk A f M g N h i m n

@[simp]
theorem tensorProductEquiv_symm_mk (i : ι)
    (x : TensorProduct (A i) (M i) (N i)) :
    (tensorProductEquiv A f M g N h).symm ⟦⟨i, x⟩⟧ =
      tensorToLimits A f M g N h i x :=
  rfl

end TensorProduct


end DirectLimit.VaryingScalar
