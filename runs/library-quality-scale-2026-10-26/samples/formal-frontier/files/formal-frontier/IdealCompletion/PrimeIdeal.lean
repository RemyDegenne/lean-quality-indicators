/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.PrimeIdeal
public import Mathlib.Order.BooleanAlgebra.Defs
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Prime ideals and Boolean-valued bounded lattice homomorphisms

A prime order ideal determines a bounded lattice homomorphism to `Bool`: elements in the
ideal map to `false`, and elements outside it map to `true`. Conversely, the false fiber
of a bounded lattice homomorphism to `Bool` is a prime order ideal. These operations
give an equivalence without assuming distributivity of the source lattice.
-/

@[expose] public section

universe u

namespace Order.Ideal

variable {A : Type u} [Lattice A] [BoundedOrder A]

/-- The characteristic bounded lattice homomorphism of a prime ideal, taking value
`false` precisely on the ideal. -/
noncomputable def IsPrime.toBoolHom {I : Ideal A} (hI : I.IsPrime) :
    BoundedLatticeHom A Bool := by
  classical
  exact {
    toFun := fun a => if a ∈ I then false else true
    map_sup' := by
      intro a b
      by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;>
        simp [I.sup_mem_iff, ha, hb]
    map_inf' := by
      intro a b
      have hmem : a ⊓ b ∈ I ↔ a ∈ I ∨ b ∈ I :=
        ⟨hI.mem_or_mem, fun h => h.elim (I.lower inf_le_left) (I.lower inf_le_right)⟩
      by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;>
        simp [hmem, ha, hb]
    map_top' := by simp [hI.toIsProper.top_notMem]
    map_bot' := by simp [I.bot_mem] }

/-- A prime ideal's characteristic map takes the value `false` exactly on the ideal. -/
@[simp] theorem IsPrime.toBoolHom_apply_eq_false_iff {I : Ideal A} (hI : I.IsPrime)
    (a : A) : hI.toBoolHom a = false ↔ a ∈ I := by
  classical
  simp [IsPrime.toBoolHom]

/-- A prime ideal's characteristic map takes the value `true` exactly off the ideal. -/
@[simp] theorem IsPrime.toBoolHom_apply_eq_true_iff {I : Ideal A} (hI : I.IsPrime)
    (a : A) : hI.toBoolHom a = true ↔ a ∉ I := by
  classical
  simp [IsPrime.toBoolHom]

end Order.Ideal

namespace BoundedLatticeHom

variable {A : Type u} [Lattice A] [BoundedOrder A]

/-- The order ideal of elements sent to `false` by a Boolean-valued bounded lattice
homomorphism. -/
def falseIdeal (f : BoundedLatticeHom A Bool) : Order.Ideal A where
  carrier := {a | f a = false}
  nonempty' := ⟨⊥, by simp⟩
  directed' := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    change f a = false at ha
    change f b = false at hb
    change f (a ⊔ b) = false
    rw [map_sup, ha, hb]
    rfl
  lower' := by
    intro a b hab hb
    change f a = false at hb
    change f b = false
    exact le_bot_iff.mp (by simpa [hb] using (OrderHomClass.monotone f hab))

/-- Membership in the false fiber is evaluation to `false`. -/
@[simp] theorem mem_falseIdeal_iff (f : BoundedLatticeHom A Bool) (a : A) :
    a ∈ f.falseIdeal ↔ f a = false := Iff.rfl

/-- The false fiber of a Boolean-valued bounded lattice homomorphism is prime. -/
theorem falseIdeal_isPrime (f : BoundedLatticeHom A Bool) : f.falseIdeal.IsPrime := by
  have hproper : f.falseIdeal.IsProper := Order.Ideal.isProper_iff_top_notMem.mpr (by simp)
  apply @Order.Ideal.IsPrime.of_mem_or_mem A _ f.falseIdeal hproper
  intro a b hab
  change f (a ⊓ b) = false at hab
  rw [map_inf] at hab
  cases hfa : f a <;> cases hfb : f b <;> simp_all [mem_falseIdeal_iff]

/-- Every Boolean-valued bounded lattice homomorphism is surjective. -/
theorem surjective_toBool (f : BoundedLatticeHom A Bool) : Function.Surjective f := by
  intro b
  cases b with
  | false => exact ⟨⊥, map_bot f⟩
  | true => exact ⟨⊤, map_top f⟩

/-- Recover a Boolean-valued bounded lattice homomorphism from its false fiber. -/
@[simp] theorem falseIdeal_toBoolHom (f : BoundedLatticeHom A Bool) :
    f.falseIdeal_isPrime.toBoolHom = f := by
  apply BoundedLatticeHom.ext
  intro a
  cases hfa : f a with
  | false => exact (f.falseIdeal_isPrime.toBoolHom_apply_eq_false_iff a).2 hfa
  | true =>
      have hnot : a ∉ f.falseIdeal := by simp [hfa]
      exact (f.falseIdeal_isPrime.toBoolHom_apply_eq_true_iff a).2 hnot

end BoundedLatticeHom

namespace Order.Ideal

variable {A : Type u} [Lattice A] [BoundedOrder A]

/-- Recover a prime ideal from the false fiber of its characteristic map. -/
@[simp] theorem IsPrime.toBoolHom_falseIdeal {I : Ideal A} (hI : I.IsPrime) :
    hI.toBoolHom.falseIdeal = I := by
  apply SetLike.ext
  intro a
  exact (BoundedLatticeHom.mem_falseIdeal_iff _ _).trans
    (hI.toBoolHom_apply_eq_false_iff a)

/-- Prime order ideals correspond to Boolean-valued bounded lattice homomorphisms. -/
noncomputable def primeEquivBoolHom :
    {I : Ideal A // I.IsPrime} ≃ BoundedLatticeHom A Bool where
  toFun I := I.property.toBoolHom
  invFun f := ⟨f.falseIdeal, f.falseIdeal_isPrime⟩
  left_inv I := by
    apply Subtype.ext
    exact I.property.toBoolHom_falseIdeal
  right_inv f := f.falseIdeal_toBoolHom

/-- The correspondence evaluates a prime ideal by its characteristic map. -/
@[simp] theorem primeEquivBoolHom_apply (I : {I : Ideal A // I.IsPrime}) :
    (primeEquivBoolHom I : BoundedLatticeHom A Bool) = I.property.toBoolHom := rfl

/-- The inverse correspondence takes a homomorphism to its false fiber. -/
@[simp] theorem primeEquivBoolHom_symm_apply (f : BoundedLatticeHom A Bool) :
    primeEquivBoolHom.symm f = ⟨f.falseIdeal, f.falseIdeal_isPrime⟩ := rfl

/-- Every prime order ideal is the false fiber of a surjective Boolean-valued
bounded lattice homomorphism. -/
theorem IsPrime.exists_boolHom {I : Ideal A} (hI : I.IsPrime) :
    ∃ f : BoundedLatticeHom A Bool, Function.Surjective f ∧
      ∀ a : A, (f a = false ↔ a ∈ I) :=
  ⟨hI.toBoolHom, hI.toBoolHom.surjective_toBool, fun a => hI.toBoolHom_apply_eq_false_iff a⟩

end Order.Ideal
