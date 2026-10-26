/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra
public import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Subcoalgebra inclusions, morphism ranges and factorization

The inclusion `Subcoalgebra.subtype` is a coalgebra homomorphism for the restricted
coalgebra structure on a subcoalgebra. A coalgebra homomorphism whose values lie in a
subcoalgebra factors uniquely through this inclusion, using `CoalgHom.codRestrict`.
Restriction recovers the identity from the inclusion and commutes with precomposition.
The source coalgebra can lie in a universe independent of the ambient coalgebra.

The source modules need only `AddCommMonoid`, `Module`, and `CoalgebraStruct`:
these maps preserve comultiplication and counit without requiring coalgebra laws on
the sources. The ambient coalgebra and its subcoalgebra retain their full coalgebra
structures over a field.

`CoalgHom.range` equips the underlying linear-map range with this restricted coalgebra
structure, and `CoalgHom.rangeRestrict` factors the homomorphism through its range. The
carrier is the existing submodule subtype. Membership, linear-map, evaluation and
factorization equations describe these constructions. Generic `CoalgHomClass` callers use
Mathlib's named `CoalgHomClass.toCoalgHom` conversion and the same constructions.

## References

The bundled maps and their extensionality and composition API follow
`Mathlib.RingTheory.Coalgebra.Hom`. Codomain restriction uses `LinearMap.codRestrict` and
`LinearMap.subtype_comp_codRestrict` from `Mathlib.Algebra.Module.Submodule.LinearMap`.
The comultiplication compatibility follows from tensor-map composition in
`Mathlib.LinearAlgebra.TensorProduct.Map` and injectivity of tensor inclusions over a
field, as in `Mathlib.RingTheory.Flat.Basic`. The range carrier and its linear restriction
are Mathlib's `LinearMap.range` and `LinearMap.rangeRestrict`. The coalgebra on that carrier
uses `Subcoalgebra.mk'` and the counit restriction and comultiplication lift from
`AlgebraicGroups.Algebra.Coalgebra.Subcoalgebra.Coalgebra`. Unique factorization uses this
module's `CoalgHom.codRestrict_unique` and `Subcoalgebra.subtype_comp_injective`.
-/

@[expose] public section

universe u v w w₁ uF

open scoped TensorProduct

namespace Subcoalgebra

variable {K : Type u} {C : Type v}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]

/-- The comultiplication of the subcoalgebra instance is the restricted comultiplication. -/
theorem coalgebra_comul_eq (D : Subcoalgebra K C) :
    Coalgebra.comul (R := K) (A := D) = D.comul :=
  rfl

/-- The counit of the subcoalgebra instance is the restricted counit. -/
theorem coalgebra_counit_eq (D : Subcoalgebra K C) :
    Coalgebra.counit (R := K) (A := D) = D.counit :=
  rfl

/-- Tensor inclusion intertwines the subcoalgebra instance's and ambient comultiplications. -/
@[simp]
theorem mapIncl_comp_coalgebra_comul (D : Subcoalgebra K C) :
    TensorProduct.mapIncl D.toSubmodule D.toSubmodule ∘ₗ
        Coalgebra.comul (R := K) (A := D) =
      Coalgebra.comul (R := K) (A := C) ∘ₗ D.toSubmodule.subtype :=
  D.mapIncl_comp_comul

/-- Comultiplication in the subcoalgebra maps to ambient comultiplication under inclusion. -/
@[simp]
theorem mapIncl_coalgebra_comul (D : Subcoalgebra K C) (x : D) :
    TensorProduct.mapIncl D.toSubmodule D.toSubmodule
        (Coalgebra.comul (R := K) (A := D) x) =
      Coalgebra.comul (R := K) (A := C) (x : C) :=
  LinearMap.congr_fun D.mapIncl_comp_coalgebra_comul x

/-- The ambient counit composed with inclusion is the counit of the subcoalgebra instance. -/
@[simp]
theorem coalgebra_counit_comp_subtype (D : Subcoalgebra K C) :
    Coalgebra.counit (R := K) (A := C) ∘ₗ D.toSubmodule.subtype =
      Coalgebra.counit (R := K) (A := D) :=
  D.counit_comp_subtype

/-- The counit of the subcoalgebra instance agrees with the ambient counit on members. -/
@[simp]
theorem coalgebra_counit_apply (D : Subcoalgebra K C) (x : D) :
    Coalgebra.counit (R := K) (A := D) x =
      Coalgebra.counit (R := K) (A := C) (x : C) :=
  D.counit_apply x

/-- The inclusion of a subcoalgebra into its ambient coalgebra. -/
noncomputable def subtype (D : Subcoalgebra K C) : D →ₗc[K] C where
  toLinearMap := D.toSubmodule.subtype
  counit_comp := D.coalgebra_counit_comp_subtype
  map_comp_comul := D.mapIncl_comp_coalgebra_comul

@[simp]
theorem subtype_toLinearMap (D : Subcoalgebra K C) :
    D.subtype.toLinearMap = D.toSubmodule.subtype :=
  rfl

@[simp]
theorem subtype_apply (D : Subcoalgebra K C) (x : D) : D.subtype x = (x : C) :=
  rfl

/-- The inclusion of a subcoalgebra is injective. -/
theorem subtype_injective (D : Subcoalgebra K C) : Function.Injective D.subtype :=
  coe_injective

variable {A : Type w} [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

/-- Coalgebra homomorphisms into a subcoalgebra are determined by their ambient values. -/
theorem coalgHom_ext {D : Subcoalgebra K C} {f g : A →ₗc[K] D}
    (h : ∀ x, (f x : C) = (g x : C)) : f = g :=
  CoalgHom.ext fun x => coe_injective (h x)

/-- Composition with the inclusion of a subcoalgebra is injective. -/
theorem subtype_comp_injective (D : Subcoalgebra K C) :
    Function.Injective (fun f : A →ₗc[K] D => D.subtype.comp f) := by
  intro f g h
  exact CoalgHom.ext fun x => D.subtype_injective (CoalgHom.congr_fun h x)

@[simp]
theorem subtype_comp_inj (D : Subcoalgebra K C) {f g : A →ₗc[K] D} :
    D.subtype.comp f = D.subtype.comp g ↔ f = g :=
  D.subtype_comp_injective.eq_iff

end Subcoalgebra

namespace CoalgHom

variable {K : Type u} {C : Type v} {A : Type w}
variable [Field K] [AddCommGroup C] [Module K C] [Coalgebra K C]
variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]

/-- Restrict the codomain of a coalgebra homomorphism to a subcoalgebra containing its values. -/
noncomputable def codRestrict (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : A →ₗc[K] D where
  toLinearMap := f.toLinearMap.codRestrict D.toSubmodule h
  counit_comp := by
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, D.coalgebra_counit_apply, LinearMap.codRestrict_apply]
    exact CoalgHomClass.counit_comp_apply f x
  map_comp_comul := by
    apply LinearMap.ext
    intro x
    apply Module.Flat.tensorProduct_mapIncl_injective_of_right D.toSubmodule D.toSubmodule
    simp only [LinearMap.comp_apply]
    calc
      TensorProduct.mapIncl D.toSubmodule D.toSubmodule
          (TensorProduct.map (f.toLinearMap.codRestrict D.toSubmodule h)
            (f.toLinearMap.codRestrict D.toSubmodule h)
            (Coalgebra.comul (R := K) (A := A) x)) =
          TensorProduct.map f.toLinearMap f.toLinearMap
            (Coalgebra.comul (R := K) (A := A) x) := by
        simp only [TensorProduct.mapIncl, TensorProduct.map_map,
          LinearMap.subtype_comp_codRestrict]
      _ = Coalgebra.comul (R := K) (A := C) (f x) :=
        CoalgHomClass.map_comp_comul_apply f x
      _ = TensorProduct.mapIncl D.toSubmodule D.toSubmodule
          (Coalgebra.comul (R := K) (A := D)
            (f.toLinearMap.codRestrict D.toSubmodule h x)) := by
        rw [D.mapIncl_coalgebra_comul, LinearMap.codRestrict_apply]
        rfl

@[simp]
theorem codRestrict_toLinearMap (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) :
    (f.codRestrict D h).toLinearMap = f.toLinearMap.codRestrict D.toSubmodule h :=
  rfl

/-- Codomain restriction sends an element to the same value, viewed as a subcoalgebra member. -/
theorem codRestrict_apply (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (x : A) : f.codRestrict D h x = ⟨f x, h x⟩ :=
  rfl

@[simp]
theorem coe_codRestrict (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (x : A) : (f.codRestrict D h x : C) = f x :=
  rfl

/-- Inclusion after codomain restriction recovers the original homomorphism. -/
@[simp]
theorem subtype_comp_codRestrict (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) : D.subtype.comp (f.codRestrict D h) = f :=
  CoalgHom.ext fun _ => rfl

/-- Restricting a subcoalgebra's inclusion back to itself is the identity. -/
@[simp]
theorem codRestrict_subtype (D : Subcoalgebra K C) :
    D.subtype.codRestrict D (fun x => Subcoalgebra.coe_mem x) = CoalgHom.id K D :=
  CoalgHom.ext fun _ => Subtype.ext rfl

/-- Restricting the ambient form of a homomorphism into a subcoalgebra recovers that
homomorphism. -/
@[simp]
theorem codRestrict_subtype_comp (D : Subcoalgebra K C) (g : A →ₗc[K] D) :
    (D.subtype.comp g).codRestrict D
        (fun x => Subcoalgebra.coe_mem (g x)) = g :=
  CoalgHom.ext fun _ => Subtype.ext rfl

/-- A factorization through a subcoalgebra inclusion is its codomain restriction. -/
theorem codRestrict_unique (f : A →ₗc[K] C) (D : Subcoalgebra K C)
    (h : ∀ x, f x ∈ D) (g : A →ₗc[K] D) (hg : D.subtype.comp g = f) :
    g = f.codRestrict D h := by
  apply D.subtype_comp_injective
  exact hg.trans (subtype_comp_codRestrict f D h).symm

/-- Two codomain restrictions are equal exactly when the original homomorphisms are equal. -/
@[simp]
theorem codRestrict_inj (D : Subcoalgebra K C) {f g : A →ₗc[K] C}
    (hf : ∀ x, f x ∈ D) (hg : ∀ x, g x ∈ D) :
    f.codRestrict D hf = g.codRestrict D hg ↔ f = g := by
  constructor
  · intro h
    have h' := congrArg (fun k : A →ₗc[K] D => D.subtype.comp k) h
    simpa only [subtype_comp_codRestrict] using h'
  · intro h
    subst g
    exact CoalgHom.ext fun _ => Subtype.ext rfl

/-- A homomorphism factors uniquely through a subcoalgebra inclusion exactly when its values
belong to the subcoalgebra. -/
theorem existsUnique_subtype_comp_iff (f : A →ₗc[K] C) (D : Subcoalgebra K C) :
    (∃! g : A →ₗc[K] D, D.subtype.comp g = f) ↔ ∀ x, f x ∈ D := by
  constructor
  · rintro ⟨g, hg, _⟩ x
    rw [← hg]
    exact Subcoalgebra.coe_mem (g x)
  · intro h
    exact ⟨f.codRestrict D h, subtype_comp_codRestrict f D h,
      fun g hg => codRestrict_unique f D h g hg⟩

variable {B : Type w₁} [AddCommMonoid B] [Module K B] [CoalgebraStruct K B]

/-- Codomain restriction commutes with precomposition by a coalgebra homomorphism. -/
@[simp]
theorem codRestrict_comp (f : B →ₗc[K] C) (g : A →ₗc[K] B) (D : Subcoalgebra K C)
    (h : ∀ y, f y ∈ D) :
    (f.comp g).codRestrict D (fun x => h (g x)) = (f.codRestrict D h).comp g :=
  CoalgHom.ext fun _ => Subtype.ext rfl

end CoalgHom

namespace CoalgHom

section ImageClosure

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R]
variable [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
variable [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]

private theorem mapIncl_map_linearRangeRestrict_comul (f : A →ₗc[R] B) (x : A) :
    TensorProduct.mapIncl (LinearMap.range f.toLinearMap) (LinearMap.range f.toLinearMap)
        (TensorProduct.map f.toLinearMap.rangeRestrict f.toLinearMap.rangeRestrict
          (Coalgebra.comul (R := R) (A := A) x)) =
      Coalgebra.comul (R := R) (A := B) (f x) := by
  simp only [TensorProduct.mapIncl, TensorProduct.map_map,
    LinearMap.subtype_comp_rangeRestrict]
  exact LinearMap.congr_fun f.map_comp_comul x

end ImageClosure

section Range

variable {K : Type u} {A : Type v} {B : Type w}
variable [Field K]
variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]
variable [AddCommGroup B] [Module K B] [Coalgebra K B]

/-- The range of a coalgebra homomorphism, with the restricted coalgebra structure on its
underlying linear-map range. The source need not satisfy the coalgebra laws. -/
def range (f : A →ₗc[K] B) : Subcoalgebra K B :=
  Subcoalgebra.mk' (LinearMap.range f.toLinearMap) (by
    rintro y ⟨x, rfl⟩
    exact ⟨TensorProduct.map f.toLinearMap.rangeRestrict f.toLinearMap.rangeRestrict
      (Coalgebra.comul (R := K) (A := A) x), mapIncl_map_linearRangeRestrict_comul f x⟩)

/-- The underlying submodule of a coalgebra homomorphism's range is its linear-map range. -/
@[simp]
theorem range_toSubmodule (f : A →ₗc[K] B) :
    f.range.toSubmodule = LinearMap.range f.toLinearMap := by
  rfl

/-- The carrier of a coalgebra homomorphism's range is its set-theoretic range. -/
@[simp]
theorem coe_range (f : A →ₗc[K] B) : (f.range : Set B) = Set.range f := by
  exact LinearMap.coe_range f.toLinearMap

/-- Membership in the range is equivalent to having a preimage. -/
@[simp]
theorem mem_range {f : A →ₗc[K] B} {y : B} : y ∈ f.range ↔ ∃ x, f x = y := by
  exact LinearMap.mem_range (f := f.toLinearMap)

/-- A coalgebra homomorphism with codomain restricted to its range. -/
noncomputable def rangeRestrict (f : A →ₗc[K] B) : A →ₗc[K] f.range :=
  f.codRestrict f.range (fun x => LinearMap.mem_range_self f.toLinearMap x)

/-- Forgetting the coalgebra structure gives the linear map restricted to its range. -/
@[simp]
theorem rangeRestrict_toLinearMap (f : A →ₗc[K] B) :
    f.rangeRestrict.toLinearMap = f.toLinearMap.rangeRestrict := by
  exact codRestrict_toLinearMap f f.range (fun x => LinearMap.mem_range_self f.toLinearMap x)

/-- Range restriction sends an element to its image, viewed as a range member. -/
theorem rangeRestrict_apply (f : A →ₗc[K] B) (x : A) :
    f.rangeRestrict x = ⟨f x, LinearMap.mem_range_self f.toLinearMap x⟩ := by
  exact codRestrict_apply f f.range (fun y => LinearMap.mem_range_self f.toLinearMap y) x

/-- Range restriction does not change the ambient value. -/
@[simp]
theorem coe_rangeRestrict (f : A →ₗc[K] B) (x : A) : (f.rangeRestrict x : B) = f x := by
  exact coe_codRestrict f f.range (fun y => LinearMap.mem_range_self f.toLinearMap y) x

/-- Inclusion after range restriction recovers the homomorphism. -/
@[simp]
theorem subtype_comp_rangeRestrict (f : A →ₗc[K] B) :
    f.range.subtype.comp f.rangeRestrict = f := by
  exact subtype_comp_codRestrict f f.range (fun x => LinearMap.mem_range_self f.toLinearMap x)

/-- Range restriction is surjective. -/
theorem surjective_rangeRestrict (f : A →ₗc[K] B) : Function.Surjective f.rangeRestrict := by
  change Function.Surjective f.rangeRestrict.toLinearMap
  rw [rangeRestrict_toLinearMap]
  exact LinearMap.surjective_rangeRestrict f.toLinearMap

/-- Every factorization through the range inclusion is the range restriction. -/
theorem rangeRestrict_unique (f : A →ₗc[K] B) (g : A →ₗc[K] f.range)
    (hg : f.range.subtype.comp g = f) : g = f.rangeRestrict := by
  exact codRestrict_unique f f.range (fun x => LinearMap.mem_range_self f.toLinearMap x) g hg

/-- Containment of the range in a submodule is equivalent to containment of every image. -/
theorem range_le_iff {f : A →ₗc[K] B} {S : Submodule K B} :
    f.range.toSubmodule ≤ S ↔ ∀ x, f x ∈ S := by
  rw [range_toSubmodule]
  constructor
  · intro h x
    exact h (LinearMap.mem_range_self f.toLinearMap x)
  · rintro h y ⟨x, rfl⟩
    exact h x

variable {D : Type w₁} [AddCommMonoid D] [Module K D] [CoalgebraStruct K D]

/-- Precomposition by range restriction is injective on coalgebra homomorphisms. -/
theorem rangeRestrict_comp_injective (f : A →ₗc[K] B) :
    Function.Injective (fun g : f.range →ₗc[K] D => g.comp f.rangeRestrict) := by
  intro g h hcomp
  apply CoalgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := f.surjective_rangeRestrict y
  exact CoalgHom.congr_fun hcomp x

end Range

end CoalgHom

namespace CoalgHomClass

section LinearMap

variable {R : Type u} {A : Type v} {B : Type w} {F : Type uF}
variable [CommSemiring R]
variable [AddCommMonoid A] [Module R A] [CoalgebraStruct R A]
variable [AddCommMonoid B] [Module R B] [CoalgebraStruct R B]
variable [FunLike F A B] [CoalgHomClass F R A B]

/-- The named bundled conversion preserves the linear map supplied by the morphism class. -/
@[simp]
theorem toCoalgHom_toLinearMap (f : F) :
    (CoalgHomClass.toCoalgHom (F := F) (R := R) (A := A) (B := B) f).toLinearMap =
      (LinearMap.ofClass f : A →ₗ[R] B) := by
  apply LinearMap.ext
  intro x
  exact congrFun
    ((CoalgHom.coe_toLinearMap
      (CoalgHomClass.toCoalgHom (F := F) (R := R) (A := A) (B := B) f)).trans
      ((CoalgHom.coe_coe (R := R) f).trans
        (LinearMap.coe_ofClass (σ := RingHom.id R) (f := f)).symm)) x

end LinearMap

variable {K : Type u} {A : Type v} {B : Type w} {F : Type uF}
variable [Field K]
variable [AddCommMonoid A] [Module K A] [CoalgebraStruct K A]
variable [AddCommGroup B] [Module K B] [Coalgebra K B]
variable [FunLike F A B] [CoalgHomClass F K A B]

/-- The range restriction of the bundled conversion agrees with linear range restriction. -/
theorem toCoalgHom_rangeRestrict_toLinearMap (f : F) :
    (CoalgHomClass.toCoalgHom (F := F) (R := K) (A := A) (B := B) f).rangeRestrict.toLinearMap =
      (LinearMap.ofClass f : A →ₗ[K] B).rangeRestrict := by
  rfl

end CoalgHomClass
