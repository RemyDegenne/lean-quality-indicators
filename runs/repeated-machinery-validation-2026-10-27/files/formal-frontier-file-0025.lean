/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicGroups.GroupObject.Hom
public import AlgebraicGroups.GroupObject.Translation
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Kernel fibres and torsors for group-object morphisms

This file relates monomorphisms from group objects to monoid objects to their fibres over
the unit, and begins the categorical core of smooth descent for extensions of group schemes.
The monomorphism criterion uses all ordinary test objects through their Hom groups. The
fibre object needs no group structure, and the target need only be a monoid object.

The source-group hypothesis is essential: addition `ℕ × ℕ → ℕ` has trivial zero fibre
but is not injective. For schemes, the fibre must be the scheme-theoretic pullback:
in characteristic `p`, Frobenius on `Gₐ` has kernel `αₚ`, which geometric points do not detect.

The chosen-lift
statement allows a monoid object as target: right translation by an ordinary
point of the source identifies the supplied kernel with the fibre over its image.
This requires neither a group structure on the kernel nor a multiplicative
chosen point, and does not assert that a fibre without a supplied lift already
has a point.

## References

* J. S. Milne, *Algebraic Groups* (2017), Definition 1.61 and the proof of
  Proposition 1.62(a), for exact sequences and the fibre-translation argument
  in smooth extension descent. The kernel-pair theorem here is a generic
  pullback statement, not the smoothness implication.
* J. S. Milne, *Abelian Varieties*, version 2.0 (March 16, 2008), Chapter I,
  proof of Proposition 7.1, for the group-target specialization of the
  chosen-lift fibre-translation step. The monoid-target statement is more general.
  Scalar extension and the existence of a lift are separate from this step;
  the full proposition is not asserted here.
* Mathlib, `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, for group laws on
  Hom sets, and the `IsPullback` cone and universal-property API;
  `Mathlib.Algebra.Group.Subgroup.Ker`, for the trivial-kernel injectivity criterion.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Category

universe v u

namespace CategoryTheory.GrpObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism from a group object to a monoid object is a monomorphism exactly when
the canonical map from the tensor unit to its fibre over the unit is an isomorphism. -/
theorem mono_iff_isIso_lift_one {N G Q : C} [GrpObj G] [MonObj Q]
    (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) :
    Mono q ↔ IsIso (hN.lift η[G] (𝟙 (𝟙_ C))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)) := by
  constructor
  · intro hq
    let : Mono q := hq
    have hunit : IsPullback η[G] (𝟙 (𝟙_ C)) q η[Q] :=
      IsPullback.of_vert_isIso_mono
        ⟨by simpa only [Category.id_comp] using IsMonHom.one_hom q⟩
    exact (IsLimit.nonempty_isLimit_iff_isIso_lift hN.isLimit).mp hunit.isLimit'
  · intro he
    let e := hN.lift η[G] (𝟙 (𝟙_ C))
      (by simpa only [Category.id_comp] using IsMonHom.one_hom q)
    let : IsIso e := he
    let hterminal : IsTerminal N := isTerminalTensorUnit.ofIso (asIso e)
    refine ⟨fun {T} a b hab ↦ ?_⟩
    have hinjective : Function.Injective (IsMonHom.monoidHom q T) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro f hf
      apply Subgroup.mem_bot.mpr
      have hfq : f ≫ q = toUnit T ≫ η[Q] := hf
      calc
        f = hN.lift f (toUnit T) hfq ≫ i := (hN.lift_fst _ _ _).symm
        _ = (toUnit T ≫ e) ≫ i :=
          congrArg (fun k : T ⟶ N ↦ k ≫ i) (hterminal.hom_ext _ _)
        _ = 1 := by simp only [Category.assoc, e, hN.lift_fst, Hom.one_def]
    exact hinjective hab

variable {N G Q : C} [GrpObj G]

section MonoidTarget

variable [MonObj Q]

/-- If `N` is the kernel of a monoid morphism from a group object `G` to a monoid
object `Q`, then `(n, g) ↦ (i(n)g, g)` exhibits `N × G` as `G ×_Q G`.
No group structure on `N` or inverse operation on `Q` is required.
Compare the fibre-translation argument in Milne, *Algebraic Groups* (2017), proof of
Proposition 1.62(a); the conclusion here is only the categorical pullback. -/
theorem isPullback_kernel_mul (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) :
    IsPullback ((i ⊗ₘ 𝟙 G) ≫ μ[G]) (snd N G) q q := by
  have hmul : (i ⊗ₘ 𝟙 G) ≫ μ[G] = (fst N G ≫ i) * snd N G := by
    rw [Hom.mul_def, ← lift_fst_comp_snd_comp]
    simp
  have hdiff (s : PullbackCone q q) : (s.fst * s.snd⁻¹) ≫ q = (toUnit s.pt) ≫ η[Q] := by
    change (s.fst * s.snd⁻¹) ≫ q = 1
    calc
      (s.fst * s.snd⁻¹) ≫ q = (s.fst ≫ q) * (s.snd⁻¹ ≫ q) :=
        MonObj.mul_comp _ _ _
      _ = (s.snd ≫ q) * (s.snd⁻¹ ≫ q) := by rw [s.condition]
      _ = (s.snd * s.snd⁻¹) ≫ q := (MonObj.mul_comp _ _ _).symm
      _ = 1 := by rw [mul_inv_cancel, MonObj.one_comp]
  let kernelLift (s : PullbackCone q q) : s.pt ⟶ N :=
    hN.lift (s.fst * s.snd⁻¹) (toUnit s.pt) (hdiff s)
  have kernelLift_i (s : PullbackCone q q) : kernelLift s ≫ i = s.fst * s.snd⁻¹ := by
    simp [kernelLift]
  have kernelLift_toUnit (s : PullbackCone q q) : kernelLift s ≫ toUnit N = toUnit s.pt := by
    simp [kernelLift]
  refine
    { w := ?_
      isLimit' := ⟨PullbackCone.IsLimit.mk _
        (fun s ↦ lift (kernelLift s) s.snd)
        ?_ ?_ ?_⟩ }
  · rw [hmul]
    rw [MonObj.mul_comp, Category.assoc, hN.w]
    simp [← Hom.one_def]
  · intro s
    rw [hmul]
    simp [MonObj.comp_mul, kernelLift_i]
  · intro s
    simp
  · intro s m hm₁ hm₂
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply hN.hom_ext
      · rw [kernelLift_i]
        rw [hmul] at hm₁
        have hm₁' : (m ≫ fst N G ≫ i) * (m ≫ snd N G) = s.fst := by
          simpa [MonObj.comp_mul, Category.assoc] using hm₁
        rw [hm₂] at hm₁'
        simpa only [Category.assoc] using (eq_mul_inv_iff_mul_eq).2 hm₁'
      · rw [kernelLift_toUnit]
        simp
    · rw [lift_snd]
      exact hm₂

end MonoidTarget

/-- For a monoid-object morphism `q` from a group object to a monoid object,
a chosen ordinary point `g` identifies the supplied kernel with the fibre over
`g ≫ q` by right translation, in the order `i(n) * g`. No monoid structure on
`N` or multiplicativity of `i` or `g` is assumed.
The group-target specialization is the chosen-lift translation step in Milne,
*Abelian Varieties*, version 2.0 (March 16, 2008), Chapter I, proof of
Proposition 7.1. The monoid-target statement does not assert that fibres without
a supplied lift already have points, nor supply the scalar-extension or
existence arguments of that proposition. -/
theorem isPullback_kernel_mulRight [MonObj Q] (i : N ⟶ G) (q : G ⟶ Q) [IsMonHom q]
    (hN : IsPullback i (toUnit N) q η[Q]) (g : 𝟙_ C ⟶ G) :
    IsPullback (i ≫ (GrpObj.mulRight g).hom) (toUnit N) q (g ≫ q) := by
  have hdiff (s : PullbackCone q (g ≫ q)) :
      (s.fst * (s.snd ≫ g)⁻¹) ≫ q = toUnit s.pt ≫ η[Q] := by
    calc
      (s.fst * (s.snd ≫ g)⁻¹) ≫ q =
          (s.fst ≫ q) * ((s.snd ≫ g)⁻¹ ≫ q) := MonObj.mul_comp _ _ _
      _ = ((s.snd ≫ g) ≫ q) * ((s.snd ≫ g)⁻¹ ≫ q) := by
        rw [s.condition, Category.assoc]
      _ = ((s.snd ≫ g) * (s.snd ≫ g)⁻¹) ≫ q := (MonObj.mul_comp _ _ _).symm
      _ = 1 := by rw [mul_inv_cancel, MonObj.one_comp]
      _ = toUnit s.pt ≫ η[Q] := Hom.one_def
  let kernelLift (s : PullbackCone q (g ≫ q)) : s.pt ⟶ N :=
    hN.lift (s.fst * (s.snd ≫ g)⁻¹) (toUnit s.pt) (hdiff s)
  have kernelLift_i (s : PullbackCone q (g ≫ q)) :
      kernelLift s ≫ i = s.fst * (s.snd ≫ g)⁻¹ := by
    simp [kernelLift]
  refine
    { w := ?_
      isLimit' := ⟨PullbackCone.IsLimit.mk _ kernelLift ?_ ?_ ?_⟩ }
  · rw [comp_mulRight_hom, MonObj.mul_comp, hN.w]
    simp only [← Hom.one_def, _root_.one_mul, Category.assoc]
  · intro s
    rw [← Category.assoc, comp_mulRight_hom, kernelLift_i,
      toUnit_unique (toUnit s.pt) s.snd]
    exact inv_mul_cancel_right _ _
  · intro s
    exact toUnit_unique _ _
  · intro s m hm₁ hm₂
    apply hN.hom_ext
    · rw [kernelLift_i]
      rw [← Category.assoc, comp_mulRight_hom,
        toUnit_unique (toUnit s.pt) s.snd] at hm₁
      exact (eq_mul_inv_iff_mul_eq).2 hm₁
    · rw [hm₂]
      exact toUnit_unique _ _

end CategoryTheory.GrpObj
