/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjectiveSmallness
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.StdBasis

/-!
# K₀ of finite projective right modules

For an arbitrary ring `R`, `KTheory.ProjectiveClass R` is the ring-sized
commutative monoid of isomorphism classes of finitely generated projective
right `R`-modules. Its zero is the zero module and its addition is binary
direct sum, modeled by the product of module carriers.

`KTheory.K0 R` is the additive Grothendieck group of this monoid. The maps
`ProjectiveClass.of` and `K0.of` accept modules in arbitrary carrier universes:
the ring-universe representatives of `ModuleCat.FiniteProjective` place them
in one reference category. Equality in `ProjectiveClass R` is module
isomorphism; equality in `K0 R` need not be module isomorphism.
`ProjectiveClass.liftFunction` descends isomorphism-invariant functions from the
reference modules to functions on their classes. `ProjectiveClass.lift` bundles
this descent as an additive map when the function preserves zero and direct sum.

## Implementation notes

The Cartesian monoidal structure used on the reference category chooses the
zero module and the ordinary binary module product explicitly. It and its
braiding are private to this construction; no tensor-product monoidal
structure on modules is used. Essential smallness supplies the prerequisite
for `Shrink`, whose existing algebraic transport resizes the class monoid.
The group completion and its universal property are Mathlib's additive
Grothendieck group, without any cancellation assumption.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, group completion and the definition of K₀.
* Mathlib's skeleton, chosen finite-product Cartesian monoidal structure,
  algebraic transport to `Shrink`, and additive Grothendieck group.
* Mathlib's finite-coordinate linear equivalence and free-module instances.
* The finite-projective category and representative formalization in this
  library, and Formal Frontier's Algebraic Direct Limits object-class
  group-completion formalization, whose skeleton-based approach this file
  follows without importing a separate completion framework.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace KTheory

variable (R : Type u) [Ring R]

private abbrev RightProjective := ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ

private def zeroCone : LimitCone (Functor.empty.{0} (RightProjective R)) where
  cone := asEmptyCone (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1})
  isLimit := IsTerminal.ofUniqueHom
    (fun X ↦ (ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ X _).symm 0)
    (fun X f ↦ by
      apply ModuleCat.FiniteProjective.hom_ext
      ext x)

private def productCone (X Y : RightProjective R) : LimitCone (pair X Y) where
  cone := BinaryFan.mk
    ((ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) X).symm (LinearMap.fst Rᵐᵒᵖ X Y))
    ((ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) Y).symm (LinearMap.snd Rᵐᵒᵖ X Y))
  isLimit := BinaryFan.IsLimit.mk _
    (fun {T} f g ↦ (ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T _).symm
      ((ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T X f).prod
        (ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T Y g)))
    (fun _ _ ↦ by apply ModuleCat.FiniteProjective.hom_ext; rfl)
    (fun _ _ ↦ by apply ModuleCat.FiniteProjective.hom_ext; rfl)
    (fun {T} f g m hf hg ↦ by
      apply ModuleCat.FiniteProjective.hom_ext
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · exact congrArg
          (fun h : T ⟶ X ↦ ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T X h x) hf
      · exact congrArg
          (fun h : T ⟶ Y ↦ ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T Y h x) hg)

@[instance_reducible]
private def directSumCartesian : CartesianMonoidalCategory (RightProjective R) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts (zeroCone R) (productCone R)

attribute [local instance] directSumCartesian

@[instance_reducible]
private def directSumBraided : BraidedCategory (RightProjective R) :=
  BraidedCategory.ofCartesianMonoidalCategory

attribute [local instance] directSumBraided

@[instance_reducible]
private def directSumSymmetric : SymmetricCategory (RightProjective R) :=
  CartesianMonoidalCategory.toSymmetricCategory

attribute [local instance] directSumSymmetric

private theorem smallAdditiveSkeleton :
    Small.{u} (Additive (Skeleton (RightProjective R))) :=
  small_map Additive.toMul

attribute [local instance] smallAdditiveSkeleton

/-- Isomorphism classes of finite projective right `R`-modules, with zero and
binary direct sum as the commutative-monoid operations, in the ring universe. -/
noncomputable def ProjectiveClass : Type u :=
  letI : Small.{u} (Additive (Skeleton (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ))) :=
    small_map Additive.toMul
  Shrink.{u} (Additive (Skeleton (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ)))

@[no_expose] noncomputable instance : AddCommMonoid (ProjectiveClass R) :=
  inferInstanceAs (AddCommMonoid (Shrink.{u} (Additive (Skeleton (RightProjective R)))))

private noncomputable def classEquiv :
    ProjectiveClass R ≃+ Additive (Skeleton (RightProjective R)) :=
  Shrink.addEquiv

namespace ProjectiveClass

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The direct-sum isomorphism class of a finite projective right module,
using its ring-universe representative. -/
@[no_expose] noncomputable def of : ProjectiveClass R :=
  (classEquiv R).symm (Additive.ofMul (ModuleCat.FiniteProjective.isoClass Rᵐᵒᵖ M))

/-- Two classes, including inputs in different carrier universes, are equal
exactly when the right modules are linearly equivalent. -/
theorem of_eq_iff (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R M = of R N ↔ Nonempty (M ≃ₗ[Rᵐᵒᵖ] N) := by
  unfold of
  rw [(classEquiv R).symm.injective.eq_iff, Additive.ofMul.injective.eq_iff]
  exact ModuleCat.FiniteProjective.isoClass_eq_iff Rᵐᵒᵖ M N

/-- Linear equivalence preserves the direct-sum isomorphism class. -/
theorem of_eq_of_equiv {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    of R M = of R N :=
  (of_eq_iff R M N).2 ⟨e⟩

/-- Passing to the ring-universe representative does not change the class. -/
@[simp]
theorem of_repr : of R (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) = of R M :=
  of_eq_of_equiv R _ (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)

/-- A carrier lift does not change the isomorphism class. -/
@[simp]
theorem of_ulift : of R (ULift.{w} M) = of R M := by
  unfold of
  rw [ModuleCat.FiniteProjective.isoClass_ulift]

/-- The class of any zero module is the monoid zero, including over the zero ring. -/
@[simp]
theorem of_zero (Z : Type v) [AddCommGroup Z] [Module Rᵐᵒᵖ Z] [Subsingleton Z] :
    of R Z = 0 := by
  apply (classEquiv R).injective
  simp only [of, AddEquiv.apply_symm_apply, map_zero]
  change ModuleCat.FiniteProjective.isoClass Rᵐᵒᵖ Z =
    (1 : Skeleton (RightProjective R))
  rw [ModuleCat.FiniteProjective.isoClass_zero, Skeleton.one_eq]
  rfl

/-- Binary direct sum of modules computes addition of isomorphism classes. -/
@[simp]
theorem of_prod (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R (M × N) = of R M + of R N := by
  apply (classEquiv R).injective
  simp only [of, AddEquiv.apply_symm_apply, map_add]
  change toSkeleton (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ (M × N)) =
    toSkeleton (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) *
      toSkeleton (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ N)
  exact (congr_toSkeleton_of_iso
    (ModuleCat.FiniteProjective.reprProdIso Rᵐᵒᵖ M N)).trans
      (Skeleton.toSkeleton_tensorObj
        (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)
        (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ N))

/-- The finite coordinate module has the class of `n` copies of the regular
right module, for arbitrary rings. -/
@[simp]
theorem of_fin_fun_eq_nsmul (n : ℕ) :
    of R (Fin n → Rᵐᵒᵖ) = n • of R Rᵐᵒᵖ := by
  induction n with
  | zero => simp only [of_zero, zero_nsmul]
  | succ n ih =>
    calc
      of R (Fin (n + 1) → Rᵐᵒᵖ) = of R (Rᵐᵒᵖ × (Fin n → Rᵐᵒᵖ)) :=
        of_eq_of_equiv R _
          (Fin.consLinearEquiv Rᵐᵒᵖ (fun _ : Fin (n + 1) ↦ Rᵐᵒᵖ)).symm
      _ = of R Rᵐᵒᵖ + of R (Fin n → Rᵐᵒᵖ) := of_prod R _ _
      _ = (n + 1) • of R Rᵐᵒᵖ := by rw [ih, succ_nsmul']

/-- Every class is the class of a module in the ring-universe reference category. -/
theorem of_surjective :
    Function.Surjective (fun X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦ of R X) := by
  intro a
  refine ⟨(fromSkeleton (RightProjective R)).obj ((classEquiv R a).toMul), ?_⟩
  apply (classEquiv R).injective
  simp only [of, AddEquiv.apply_symm_apply, ModuleCat.FiniteProjective.isoClass_of,
    toSkeleton_fromSkeleton_obj, ofMul_toMul]

/-- To prove a proposition about a class, it suffices to prove it on classes
of modules in the ring-universe reference category. -/
@[elab_as_elim]
theorem induction_on {p : ProjectiveClass R → Prop} (a : ProjectiveClass R)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, p (of R X)) : p a := by
  obtain ⟨X, rfl⟩ := of_surjective R a
  exact h X

/-- Additive maps out of the class monoid are determined by their values on
finite projective module classes. -/
@[ext]
theorem addHom_ext {A : Type w} [AddZero A] {f g : ProjectiveClass R →+ A}
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, f (of R X) = g (of R X)) :
    f = g := by
  apply AddMonoidHom.ext
  intro a
  exact induction_on R a h

section LiftFunction

variable {A : Type w}
  (f : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ → A)
  (hiso : ∀ {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y)

/-- Descend an isomorphism-invariant function on finite projective right modules
to a function on their isomorphism classes, with no algebraic structure on the target. -/
@[no_expose]
noncomputable def liftFunction : ProjectiveClass R → A :=
  fun a ↦ Quotient.lift (s := isIsomorphicSetoid (RightProjective R)) f
    (fun _ _ e ↦ hiso (Classical.choice e)) ((classEquiv R a).toMul)

/-- The descended function evaluates on a reference-module class as the supplied function. -/
@[simp]
theorem liftFunction_of (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    liftFunction R f hiso (of R X) = f X := by
  simp only [liftFunction, of, AddEquiv.apply_symm_apply, toMul_ofMul,
    ModuleCat.FiniteProjective.isoClass_of, Quotient.lift_mk]

/-- For an input in any carrier universe, the descended function evaluates the
supplied function on its ring-universe representative. -/
theorem liftFunction_of_module :
    liftFunction R f hiso (of R M) =
      f (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) := by
  rw [← of_repr R M]
  exact liftFunction_of R f hiso (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)

/-- A descended function is uniquely determined by its values on reference-module classes. -/
theorem liftFunction_unique (F : ProjectiveClass R → A)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, F (of R X) = f X) :
    F = liftFunction R f hiso := by
  funext a
  exact induction_on R a (fun X ↦ (h X).trans (liftFunction_of R f hiso X).symm)

end LiftFunction

section Lift

variable {A : Type w} [AddZero A]
  (f : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ → A)
  (hiso : ∀ {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y)
  (hzero : f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1}) = 0)
  (hadd : ∀ X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
    f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) = f X + f Y)

/-- Descend an isomorphism-invariant function on finite projective right modules
which preserves zero and direct sum to an additive map on their class monoid. -/
@[no_expose]
noncomputable def lift : ProjectiveClass R →+ A where
  toFun := liftFunction R f hiso
  map_zero' := by
    simpa only [of_zero] using
      (liftFunction_of R f hiso
        (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1})).trans hzero
  map_add' a b := by
    obtain ⟨X, rfl⟩ := of_surjective R a
    obtain ⟨Y, rfl⟩ := of_surjective R b
    rw [← of_prod R X Y]
    calc
      liftFunction R f hiso (of R (X × Y)) =
          f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) :=
        liftFunction_of R f hiso (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y))
      _ = f X + f Y := hadd X Y
      _ = liftFunction R f hiso (of R X) + liftFunction R f hiso (of R Y) := by
        rw [liftFunction_of, liftFunction_of]

/-- Forgetting the additive structure of the descended map gives the function descent. -/
theorem coe_lift :
    (lift R f hiso hzero hadd : ProjectiveClass R → A) = liftFunction R f hiso := by
  rfl

/-- The descended map evaluates on a reference-module class as the supplied function. -/
@[simp]
theorem lift_of (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    lift R f hiso hzero hadd (of R X) = f X :=
  liftFunction_of R f hiso X

/-- For an input in any carrier universe, the descended map evaluates the
supplied function on its ring-universe representative. -/
theorem lift_of_module :
    lift R f hiso hzero hadd (of R M) =
      f (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) := by
  exact liftFunction_of_module R M f hiso

/-- A descended additive map is uniquely determined by its values on module classes. -/
theorem lift_unique (F : ProjectiveClass R →+ A)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, F (of R X) = f X) :
    F = lift R f hiso hzero hadd := by
  apply AddMonoidHom.ext
  intro a
  exact congrFun (liftFunction_unique R f hiso F h) a

end Lift

end ProjectiveClass

/-- The additive Grothendieck group of the direct-sum isomorphism-class monoid
of finite projective right `R`-modules. -/
abbrev K0 : Type u := Algebra.GrothendieckAddGroup (ProjectiveClass R)

namespace K0

/-- The canonical additive map from direct-sum isomorphism classes to K₀.
It is not asserted to be injective. -/
noncomputable abbrev ofClass : ProjectiveClass R →+ K0 R :=
  Algebra.GrothendieckAddGroup.of

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The K₀ generator associated to a finite projective right module in any
carrier universe. -/
noncomputable def of : K0 R := ofClass R (ProjectiveClass.of R M)

/-- The canonical completion map sends a module's isomorphism class to its K₀ generator. -/
@[simp]
theorem ofClass_of : ofClass R (ProjectiveClass.of R M) = of R M := rfl

/-- Right-linear equivalence preserves the K₀ generator. The converse is not
asserted: equality after group completion is weaker than module isomorphism. -/
theorem of_eq_of_equiv {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    of R M = of R N :=
  congrArg (ofClass R) (ProjectiveClass.of_eq_of_equiv R M e)

/-- A carrier lift does not change the K₀ generator. -/
@[simp]
theorem of_ulift : of R (ULift.{w} M) = of R M := by
  simp only [of, ProjectiveClass.of_ulift]

/-- Every zero module gives the zero K₀ generator, without a nontrivial-ring premise. -/
@[simp]
theorem of_zero (Z : Type v) [AddCommGroup Z] [Module Rᵐᵒᵖ Z] [Subsingleton Z] :
    of R Z = 0 := by
  simp only [of, ProjectiveClass.of_zero, map_zero]

/-- Direct sum gives addition of K₀ generators. -/
@[simp]
theorem of_prod (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R (M × N) = of R M + of R N := by
  simp only [of, ProjectiveClass.of_prod, map_add]

/-- The group-completion universal property: additive maps from the class
monoid to any additive commutative group extend uniquely to K₀. -/
noncomputable def lift {G : Type w} [AddCommGroup G] :
    (ProjectiveClass R →+ G) ≃ (K0 R →+ G) :=
  Algebra.GrothendieckAddGroup.lift

/-- Restricting a K₀ homomorphism along the class map is the inverse universal map. -/
@[simp]
theorem lift_symm_apply {G : Type w} [AddCommGroup G] (f : K0 R →+ G) :
    (lift R).symm f = f.comp (ofClass R) := rfl

/-- The universal extension agrees with the given map on class generators. -/
@[simp]
theorem lift_ofClass {G : Type w} [AddCommGroup G]
    (f : ProjectiveClass R →+ G) (a : ProjectiveClass R) :
    lift R f (ofClass R a) = f a :=
  congrArg (fun h : ProjectiveClass R →+ G ↦ h a) ((lift R).symm_apply_apply f)

/-- Evaluation of the universal extension on a module generator. -/
@[simp]
theorem lift_of {G : Type w} [AddCommGroup G] (f : ProjectiveClass R →+ G) :
    lift R f (of R M) = f (ProjectiveClass.of R M) :=
  lift_ofClass R f (ProjectiveClass.of R M)

/-- K₀ homomorphisms are determined by their values on the class monoid. -/
theorem hom_ext_ofClass {G : Type w} [AddCommGroup G] {f g : K0 R →+ G}
    (h : ∀ a : ProjectiveClass R, f (ofClass R a) = g (ofClass R a)) : f = g := by
  apply (lift R).symm.injective
  exact AddMonoidHom.ext h

/-- K₀ homomorphisms are determined by values on finite projective module generators. -/
@[ext]
theorem hom_ext {G : Type w} [AddCommGroup G] {f g : K0 R →+ G}
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, f (of R X) = g (of R X)) :
    f = g := by
  apply hom_ext_ofClass R
  intro a
  obtain ⟨X, rfl⟩ := ProjectiveClass.of_surjective R a
  exact h X

end K0

end KTheory
