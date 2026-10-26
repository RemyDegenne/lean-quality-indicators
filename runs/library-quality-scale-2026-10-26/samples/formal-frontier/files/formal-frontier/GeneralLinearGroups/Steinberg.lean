/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import GeneralLinearGroups.ElementaryCommutator

/-!
# Finite-rank Steinberg presentation

This is the group presented by off-diagonal elementary symbols and the three
additive, disjoint and ordered-composable Steinberg relations over any ring.
The presentation is meaningful for every index type; its usual Steinberg-group
interpretation is at rank at least three. No relation is imposed between
opposite roots.
-/

set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

/-- An ordered off-diagonal position. -/
abbrev Root (ι : Type uι) := { p : ι × ι // p.1 ≠ p.2 }

/-- The off-diagonal position from `i` to `j`. -/
def root {ι : Type uι} (i j : ι) (hij : i ≠ j) : Root ι := ⟨(i, j), hij⟩

/-- An off-diagonal position and a ring coefficient. -/
abbrev Generator (ι : Type uι) (R : Type uR) := Root ι × R

variable {ι : Type uι} {R : Type uR} [Ring R]

/-- A single generator in the free group on elementary symbols. -/
def word (p : Root ι) (a : R) : FreeGroup (Generator ι R) := FreeGroup.of (p, a)

/-- Precisely the additive, noncomposable and ordered-composable relators.
No opposite-root relator is part of this set. -/
def relations : Set (FreeGroup (Generator ι R)) :=
  {w | (∃ (p : Root ι) (a b : R),
      w = word p a * word p b * (word p (a + b))⁻¹) ∨
    (∃ (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
      (_hjk : j ≠ k) (_hli : l ≠ i) (a b : R),
      w = ⁅word (root i j hij) a, word (root k l hkl) b⁆) ∨
    (∃ (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (a b : R),
      w = ⁅word (root i j hij) a, word (root j k hjk) b⁆ *
        (word (root i k hik) (a * b))⁻¹) }

/-- The group with the three explicit Steinberg relations. -/
abbrev Presented (ι : Type uι) (R : Type uR) [Ring R] :=
  PresentedGroup (relations (ι := ι) (R := R))

/-- A presented elementary symbol. -/
def generator (p : Root ι) (a : R) : Presented ι R := PresentedGroup.of (p, a)

/-- Symbols in the same position add their coefficients. -/
theorem generator_add (p : Root ι) (a b : R) :
    generator p a * generator p b = generator p (a + b) := by
  have h := PresentedGroup.one_of_mem (rels := relations (ι := ι) (R := R))
    (show word p a * word p b * (word p (a + b))⁻¹ ∈ relations from
      Or.inl ⟨p, a, b, rfl⟩)
  change generator p a * generator p b * (generator p (a + b))⁻¹ = 1 at h
  exact eq_of_mul_inv_eq_one h

@[simp]
theorem generator_zero (p : Root ι) : generator p (0 : R) = 1 := by
  have h := generator_add p (0 : R) 0
  have heq : generator p (0 : R) * generator p 0 = generator p 0 * 1 := by
    simpa using h
  exact mul_left_cancel heq

@[simp]
theorem generator_neg (p : Root ι) (a : R) :
    generator p (-a) = (generator p a)⁻¹ := by
  have h : generator p a * generator p (-a) = 1 := by
    simpa using generator_add p a (-a)
  calc
    generator p (-a) = (generator p a)⁻¹ * (generator p a * generator p (-a)) := by
      group
    _ = (generator p a)⁻¹ := by rw [h, mul_one]

/-- Symbols in two noncomposable off-diagonal positions commute. -/
theorem generator_commutator_disjoint (i j k l : ι)
    (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    (a b : R) :
    ⁅generator (root i j hij) a, generator (root k l hkl) b⁆ = 1 := by
  exact PresentedGroup.one_of_mem (rels := relations (ι := ι) (R := R))
    (Or.inr (Or.inl ⟨i, j, k, l, hij, hkl, hjk, hli, a, b, rfl⟩))

/-- The ordered three-index commutator has coefficient `a * b`. -/
theorem generator_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅generator (root i j hij) a, generator (root j k hjk) b⁆ =
      generator (root i k hik) (a * b) := by
  have h := PresentedGroup.one_of_mem (rels := relations (ι := ι) (R := R))
    (show ⁅word (root i j hij) a, word (root j k hjk) b⁆ *
      (word (root i k hik) (a * b))⁻¹ ∈ relations from
      Or.inr (Or.inr ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩))
  change ⁅generator (root i j hij) a, generator (root j k hjk) b⁆ *
    (generator (root i k hik) (a * b))⁻¹ = 1 at h
  exact eq_of_mul_inv_eq_one h

/-- Reversing a composable commutator reverses the order of coefficient multiplication. -/
theorem generator_commutator_reverse (i j k : ι)
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (a b : R) :
    ⁅generator (root i j hij) a, generator (root k i hki) b⁆ =
      generator (root k j hkj) (-(b * a)) := by
  rw [← commutatorElement_inv]
  rw [generator_commutator k i j hki hij hkj b a]
  exact (generator_neg (root k j hkj) (b * a)).symm

/-- Extend any family satisfying exactly these three laws to a group homomorphism. -/
def lift {G : Type uG} [Group G] (f : Root ι → R → G)
    (hadd : ∀ p a b, f p a * f p b = f p (a + b))
    (hdisjoint : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l)
      (_hjk : j ≠ k) (_hli : l ≠ i) (a b : R),
      ⁅f (root i j hij) a, f (root k l hkl) b⁆ = 1)
    (hcomposable : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k)
      (hik : i ≠ k) (a b : R),
      ⁅f (root i j hij) a, f (root j k hjk) b⁆ = f (root i k hik) (a * b)) :
    Presented ι R →* G :=
  PresentedGroup.toGroup (f := fun gen => f gen.1 gen.2) (by
    intro w hw
    rcases hw with ⟨p, a, b, rfl⟩ | ⟨i, j, k, l, hij, hkl, hjk, hli, a, b, rfl⟩ |
        ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩
    · simp only [word, map_mul, map_inv, FreeGroup.lift_apply_of, hadd, mul_inv_cancel]
    · simpa only [word, map_commutatorElement, FreeGroup.lift_apply_of] using
        hdisjoint i j k l hij hkl hjk hli a b
    · simp only [word, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [hcomposable i j k hij hjk hik a b, mul_inv_cancel])

@[simp]
theorem lift_generator {G : Type uG} [Group G] (f : Root ι → R → G)
    (hadd hdisjoint hcomposable) (p : Root ι) (a : R) :
    lift f hadd hdisjoint hcomposable (generator p a) = f p a :=
  PresentedGroup.toGroup.of _

/-- Agreement on generators determines a homomorphism out of the presentation. -/
@[ext]
theorem hom_ext {G : Type uG} [Group G] {φ ψ : Presented ι R →* G}
    (h : ∀ p a, φ (generator p a) = ψ (generator p a)) : φ = ψ := by
  apply PresentedGroup.ext
  rintro ⟨p, a⟩
  exact h p a

/-- The universal extension is unique when its generator evaluations are fixed. -/
theorem lift_unique {G : Type uG} [Group G] (f : Root ι → R → G)
    (hadd hdisjoint hcomposable) (φ : Presented ι R →* G)
    (hφ : ∀ p a, φ (generator p a) = f p a) :
    φ = lift f hadd hdisjoint hcomposable := by
  apply hom_ext
  intro p a
  rw [hφ, lift_generator]

section Elementary

variable [Fintype ι] [DecidableEq ι]

/-- An elementary unit viewed in the subgroup it generates. -/
def elementaryGenerator (p : Root ι) (a : R) :
    Matrix.GeneralLinearGroup.elementarySubgroup ι R :=
  ⟨Matrix.GeneralLinearGroup.elementaryUnit p.1.1 p.1.2 p.2 a,
    Matrix.GeneralLinearGroup.elementaryUnit_mem p.1.1 p.1.2 p.2 a⟩

/-- The canonical homomorphism from the presentation onto the elementary subgroup. -/
def toElementary : Presented ι R →* Matrix.GeneralLinearGroup.elementarySubgroup ι R :=
  lift elementaryGenerator
    (by
      intro p a b
      apply Subtype.ext
      exact Matrix.GeneralLinearGroup.elementaryUnit_mul_same p.1.1 p.1.2 p.2 a b)
    (by
      intro i j k l hij hkl hjk hli a b
      apply Subtype.ext
      exact (Matrix.GeneralLinearGroup.elementaryUnit_commute_disjoint
        i j k l hij hkl hjk hli a b).commutator_eq)
    (by
      intro i j k hij hjk hik a b
      apply Subtype.ext
      exact Matrix.GeneralLinearGroup.elementaryUnit_commutator
        i j k hij hjk hik a b)

@[simp]
theorem toElementary_generator (p : Root ι) (a : R) :
    toElementary (generator p a) = elementaryGenerator p a := lift_generator ..

/-- The composite of the canonical map with elementary-subgroup inclusion. -/
def toGL : Presented ι R →* Matrix.GeneralLinearGroup ι R :=
  (Matrix.GeneralLinearGroup.elementarySubgroup ι R).subtype.comp toElementary

@[simp]
theorem toGL_generator (p : Root ι) (a : R) :
    toGL (generator p a) =
      Matrix.GeneralLinearGroup.elementaryUnit p.1.1 p.1.2 p.2 a := by
  simp [toGL, elementaryGenerator]

/-- Every elementary-subgroup element has a preimage in the presented group. -/
theorem toElementary_surjective : Function.Surjective (toElementary (ι := ι) (R := R)) := by
  have hrange : Matrix.GeneralLinearGroup.elementarySubgroup ι R ≤
      (toGL (ι := ι) (R := R)).range := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, j, hij, a, rfl⟩
    exact ⟨generator (root i j hij) a, toGL_generator (root i j hij) a⟩
  intro g
  obtain ⟨x, hx⟩ := hrange g.property
  exact ⟨x, Subtype.ext hx⟩

/-- The image in the ambient general linear group is exactly the elementary subgroup. -/
theorem toGL_range : (toGL (ι := ι) (R := R)).range =
    Matrix.GeneralLinearGroup.elementarySubgroup ι R := by
  apply le_antisymm
  · rintro g ⟨x, rfl⟩
    exact (toElementary x).property
  · intro g hg
    obtain ⟨x, hx⟩ := toElementary_surjective (⟨g, hg⟩ :
      Matrix.GeneralLinearGroup.elementarySubgroup ι R)
    exact ⟨x, congrArg Subtype.val hx⟩

end Elementary

end Steinberg
