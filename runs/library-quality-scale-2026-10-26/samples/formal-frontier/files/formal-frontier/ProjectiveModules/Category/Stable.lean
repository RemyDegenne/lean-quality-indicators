/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents (stable-category contribution); see docs/CREDITS.md
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The stable category of modules

This file constructs the stable category of left modules over an arbitrary ring. Its morphisms are
module homomorphisms modulo those that factor through a projective module.

The quotient works without finiteness, commutativity, or nontriviality assumptions. When the ring
is small in the module universe, equality in the quotient is also detected by the action of a
morphism on first `Ext` groups.
-/

@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ZeroObject

namespace ModuleCat

variable (R : Type uR) [Ring R]

/-- A module morphism factors through a projective module. -/
def FactorsThroughProjective {M N : ModuleCat.{uM} R} (f : M ⟶ N) : Prop :=
  ∃ (P : ModuleCat.{uM} R), CategoryTheory.Projective P ∧
    ∃ (i : M ⟶ P) (p : P ⟶ N), f = i ≫ p

namespace FactorsThroughProjective

variable {R}

lemma zero {M N : ModuleCat.{uM} R} :
    FactorsThroughProjective R (0 : M ⟶ N) := by
  refine ⟨(0 : ModuleCat.{uM} R), inferInstance, 0, 0, ?_⟩
  simp

lemma add {M N : ModuleCat.{uM} R} {f g : M ⟶ N}
    (hf : FactorsThroughProjective R f) (hg : FactorsThroughProjective R g) :
    FactorsThroughProjective R (f + g) := by
  obtain ⟨P, hP, i, p, rfl⟩ := hf
  obtain ⟨Q, hQ, j, q, rfl⟩ := hg
  let _ : CategoryTheory.Projective P := hP
  let _ : CategoryTheory.Projective Q := hQ
  refine ⟨P ⊞ Q, inferInstance, biprod.lift i j, biprod.desc p q, ?_⟩
  simp

lemma neg {M N : ModuleCat.{uM} R} {f : M ⟶ N}
    (hf : FactorsThroughProjective R f) :
    FactorsThroughProjective R (-f) := by
  obtain ⟨P, hP, i, p, rfl⟩ := hf
  exact ⟨P, hP, i, -p, by simp⟩

lemma sub {M N : ModuleCat.{uM} R} {f g : M ⟶ N}
    (hf : FactorsThroughProjective R f) (hg : FactorsThroughProjective R g) :
    FactorsThroughProjective R (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma precomp {L M N : ModuleCat.{uM} R} (e : L ⟶ M) {f : M ⟶ N}
    (hf : FactorsThroughProjective R f) :
    FactorsThroughProjective R (e ≫ f) := by
  obtain ⟨P, hP, i, p, rfl⟩ := hf
  exact ⟨P, hP, e ≫ i, p, by simp⟩

lemma postcomp {M N L : ModuleCat.{uM} R} {f : M ⟶ N} (e : N ⟶ L)
    (hf : FactorsThroughProjective R f) :
    FactorsThroughProjective R (f ≫ e) := by
  obtain ⟨P, hP, i, p, rfl⟩ := hf
  exact ⟨P, hP, i, p ≫ e, by simp⟩

lemma of_projective_source {M N : ModuleCat.{uM} R} [CategoryTheory.Projective M]
    (f : M ⟶ N) : FactorsThroughProjective R f :=
  ⟨M, inferInstance, 𝟙 M, f, by simp⟩

lemma of_projective_target {M N : ModuleCat.{uM} R} [CategoryTheory.Projective N]
    (f : M ⟶ N) : FactorsThroughProjective R f :=
  ⟨N, inferInstance, f, 𝟙 N, by simp⟩

end FactorsThroughProjective

/-- The congruence on module morphisms whose differences factor through projective modules. -/
def stableHomRel : HomRel (ModuleCat.{uM} R) :=
  fun _ _ f g ↦ FactorsThroughProjective R (f - g)

namespace stableHomRel

variable {R}

instance : Congruence (stableHomRel.{uR, uM} R) where
  equivalence := {
    refl := fun f ↦ by
      simpa [stableHomRel] using
        (FactorsThroughProjective.zero (R := R) (M := _) (N := _))
    symm := fun {f g} h ↦ by
      change FactorsThroughProjective R (g - f)
      rw [show g - f = -(f - g) by abel]
      exact h.neg
    trans := fun {f g h} hfg hgh ↦ by
      change FactorsThroughProjective R (f - h)
      rw [show f - h = (f - g) + (g - h) by abel]
      exact hfg.add hgh }
  comp_left := by
    intro X Y Z e f g h
    change FactorsThroughProjective R (e ≫ f - e ≫ g)
    rw [← Preadditive.comp_sub]
    exact h.precomp e
  comp_right := by
    intro X Y Z f g e h
    change FactorsThroughProjective R (f ≫ e - g ≫ e)
    rw [← Preadditive.sub_comp]
    exact h.postcomp e

lemma add {M N : ModuleCat.{uM} R} (f₁ f₂ g₁ g₂ : M ⟶ N)
    (hf : stableHomRel R f₁ f₂) (hg : stableHomRel R g₁ g₂) :
    stableHomRel R (f₁ + g₁) (f₂ + g₂) := by
  change FactorsThroughProjective R ((f₁ + g₁) - (f₂ + g₂))
  rw [show (f₁ + g₁) - (f₂ + g₂) = (f₁ - f₂) + (g₁ - g₂) by abel]
  exact FactorsThroughProjective.add hf hg

end stableHomRel

/-- The stable category of left `R`-modules, modulo maps through projective modules. -/
abbrev Stable := CategoryTheory.Quotient (stableHomRel.{uR, uM} R)

namespace Stable

@[instance_reducible]
instance stablePreadditive : Preadditive (Stable.{uR, uM} R) :=
  CategoryTheory.Quotient.preadditive _
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦ stableHomRel.add f₁ f₂ g₁ g₂ hf hg)

/-- The additive quotient functor from modules to their stable category. -/
abbrev quotient : ModuleCat.{uM} R ⥤ Stable.{uR, uM} R :=
  CategoryTheory.Quotient.functor (stableHomRel R)

instance : (quotient.{uR, uM} R).Additive :=
  CategoryTheory.Quotient.functor_additive _
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦ stableHomRel.add f₁ f₂ g₁ g₂ hf hg)

variable {R}

/-- Equality in the stable category is exactly equality modulo a map through a projective. -/
lemma quotient_map_eq_iff {M N : ModuleCat.{uM} R} (f g : M ⟶ N) :
    (quotient R).map f = (quotient R).map g ↔
      FactorsThroughProjective R (f - g) :=
  CategoryTheory.Quotient.functor_map_eq_iff _ _ _

/-- A map through a projective module is zero in the stable category. -/
lemma quotient_map_eq_zero_iff {M N : ModuleCat.{uM} R} (f : M ⟶ N) :
    (quotient R).map f = 0 ↔ FactorsThroughProjective R f := by
  rw [← (quotient R).map_zero, quotient_map_eq_iff]
  simp

/-- The projector onto a summand complementary to a projective module is the identity in the
stable category. -/
@[simp]
lemma quotient_map_fst_comp_inl (M P : ModuleCat.{uM} R) [CategoryTheory.Projective P] :
    (quotient R).map ((biprod.fst : M ⊞ P ⟶ M) ≫ biprod.inl) = 𝟙 _ := by
  rw [← (quotient R).map_id]
  apply (quotient_map_eq_iff _ _).2
  refine ⟨P, inferInstance, biprod.snd, -biprod.inr, ?_⟩
  rw [Preadditive.comp_neg, ← biprod.total]
  abel

/-- Adjoining a projective direct summand does not change a module in the stable category. -/
@[simps]
noncomputable def addProjectiveIso (M P : ModuleCat.{uM} R) [CategoryTheory.Projective P] :
    (quotient R).obj M ≅ (quotient R).obj (M ⊞ P) where
  hom := (quotient R).map (biprod.inl : M ⟶ M ⊞ P)
  inv := (quotient R).map (biprod.fst : M ⊞ P ⟶ M)
  hom_inv_id := by
    rw [← (quotient R).map_comp, biprod.inl_fst, (quotient R).map_id]
  inv_hom_id := by
    rw [← (quotient R).map_comp]
    exact quotient_map_fst_comp_inl M P

/-- Every morphism with projective source is zero in the stable category. -/
@[simp]
lemma quotient_map_of_projective_source {M N : ModuleCat.{uM} R}
    [CategoryTheory.Projective M] (f : M ⟶ N) :
    (quotient R).map f = 0 :=
  (quotient_map_eq_zero_iff f).2 (.of_projective_source f)

/-- Every morphism with projective target is zero in the stable category. -/
@[simp]
lemma quotient_map_of_projective_target {M N : ModuleCat.{uM} R}
    [CategoryTheory.Projective N] (f : M ⟶ N) :
    (quotient R).map f = 0 :=
  (quotient_map_eq_zero_iff f).2 (.of_projective_target f)

end Stable

namespace FactorsThroughProjective

variable {R}

/-- A morphism factors through a projective module exactly when it acts by zero on every first
`Ext` group by precomposition. -/
lemma iff_ext_one_precomp_eq_zero [Small.{uM} R] {M N : ModuleCat.{uM} R} (f : M ⟶ N) :
    FactorsThroughProjective R f ↔
      ∀ (A : ModuleCat.{uM} R),
        (Ext.mk₀ f).precomp A (zero_add 1) = 0 := by
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩ A
    let _ : CategoryTheory.Projective P := hP
    ext e
    change (Ext.mk₀ (i ≫ p)).comp e (zero_add 1) = 0
    rw [← Ext.mk₀_comp_mk₀_assoc]
    rw [Ext.eq_zero_of_projective ((Ext.mk₀ p).comp e (zero_add 1))]
    simp
  · intro h
    let P : ModuleCat.{uM} R := CategoryTheory.Projective.over N
    let p : P ⟶ N := CategoryTheory.Projective.π N
    let S : ShortComplex (ModuleCat.{uM} R) :=
      ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel p) }
    have hf : (Ext.mk₀ f).comp hS.extClass (zero_add 1) = 0 := by
      have hf' := DFunLike.congr_fun (h (kernel p)) hS.extClass
      exact hf'
    obtain ⟨e, he⟩ := Ext.covariant_sequence_exact₃ M hS (Ext.mk₀ f) rfl hf
    refine ⟨P, inferInstance, Ext.addEquiv₀ e, p, ?_⟩
    apply (Ext.mk₀_bijective _ _).1
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
    exact he.symm

/-- Two module morphisms have the same effect by precomposition on all first `Ext` groups exactly
when their difference factors through a projective module. -/
lemma sub_iff_ext_one_precomp_eq [Small.{uM} R] {M N : ModuleCat.{uM} R} (f g : M ⟶ N) :
    FactorsThroughProjective R (f - g) ↔
      ∀ (A : ModuleCat.{uM} R),
        (Ext.mk₀ f).precomp A (zero_add 1) =
          (Ext.mk₀ g).precomp A (zero_add 1) := by
  rw [iff_ext_one_precomp_eq_zero]
  constructor
  · intro h A
    ext e
    have he := DFunLike.congr_fun (h A) e
    change (Ext.mk₀ f).comp e (zero_add 1) = (Ext.mk₀ g).comp e (zero_add 1)
    have hmk : Ext.mk₀ (f - g) = Ext.mk₀ f - Ext.mk₀ g := by
      rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, sub_eq_add_neg]
    change (Ext.mk₀ (f - g)).comp e (zero_add 1) = 0 at he
    rw [hmk, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp] at he
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)
  · intro h A
    ext e
    have he := DFunLike.congr_fun (h A) e
    change (Ext.mk₀ f).comp e (zero_add 1) = (Ext.mk₀ g).comp e (zero_add 1) at he
    change (Ext.mk₀ (f - g)).comp e (zero_add 1) = 0
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp]
    simpa only [sub_eq_add_neg] using (sub_eq_zero.mpr he)

end FactorsThroughProjective

end ModuleCat
