/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism.
-- See docs/CREDITS.md for mathematical and interface credit.
module

public import SphereTopology.Homology.Singular.MayerVietoris
public import SphereTopology.Homology.Singular.Components
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Instances.Discrete

/-!
# Reduced singular homology with integer coefficients

This file defines reduced singular homology in degree zero as the kernel of the
total augmentation `H₀(X; ℤ) ⟶ ℤ`.  The augmentation is proved natural, so
continuous maps restrict functorially to these kernels.  In positive degrees,
the reduced theory is definitionally the ordinary integer singular homology
functor.

Our convention is nonnegative and applies to every space, including the empty
space: degree zero is always the augmentation kernel, while every positive
degree is ordinary homology.  In particular, no nonemptiness instance is used
in the definitions.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 14, §§1 and 3,
  for reduced homology and the two-point computation, and Chapters 13 and 15
  for the path-component description. May's based-relative reduced theory
  is background; no comparison to this nonnegative augmentation-kernel model
  or to normalized chains is supplied here.
* Joël Riou's Mathlib degree-zero singular-homology coproduct, augmentation and
  homotopy-invariance formalizations supply the ordinary theory.
* Formal Frontier Agents' earlier reduced-homology constructions and their
  universe-polymorphic reconciliation, and the component-kernel construction
  in `SphereTopology.Homology.Singular.Components`; see `docs/CREDITS.md`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

noncomputable section

namespace AlgebraicTopology

universe u

/-- Integral singular homology, functorially in the topological space. Its
objects are the `integralSingularHomology` groups. -/
noncomputable abbrev integralSingularHomologyFunctor (n : ℕ) :=
  (singularHomologyFunctor (ModuleCat.{u, 0} ℤ) n).obj integerCoefficients

theorem integralSingularHomologyFunctor_map {X Y : TopCat.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    (integralSingularHomologyFunctor n).map f =
      HomologicalComplex.homologyMap (integralSingularChainMap f) n := by
  rfl

end AlgebraicTopology

namespace TopCat

universe u

open ContinuousMap

/-- The integer coefficient object, lifted to the universe of the spaces under
consideration. This coefficient object is used by the ordinary
integral singular-chain and Mayer--Vietoris APIs. -/
abbrev singularHomologyIntegerCoefficients : ModuleCat.{u, 0} ℤ :=
  AlgebraicTopology.integerCoefficients

/-- Compatibility name for the integral singular homology functor. -/
noncomputable abbrev integerSingularHomologyFunctor (n : ℕ) :
    TopCat.{u} ⥤ ModuleCat.{u, 0} ℤ :=
  integralSingularHomologyFunctor n

end TopCat

namespace SSet

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  [Preadditive C] [CategoryWithHomology C]

/-- The degree-zero homology class represented by a vertex of a simplicial set. -/
noncomputable def homologyZeroPoint (X : SSet.{w}) (R : C) (x : X _⦋0⦌) :
    R ⟶ X.homology R 0 :=
  (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
    (X.chainComplex R).homologyπ 0

@[reassoc]
theorem homologyZeroPoint_homology₀Iso (X : SSet.{w}) (R : C) (x : X _⦋0⦌) :
    homologyZeroPoint X R x ≫ (X.homology₀Iso R).hom =
      Sigma.ι (fun _ : X.π₀ ↦ R) (.mk x) := by
  dsimp only [homologyZeroPoint]
  simpa only [Category.assoc] using
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x

@[reassoc (attr := simp)]
theorem homologyZeroPoint_augmentation (X : SSet.{w}) (R : C) (x : X _⦋0⦌) :
    homologyZeroPoint X R x ≫ X.homology₀ε R = 𝟙 R := by
  dsimp only [homologyZeroPoint]
  simpa only [Category.assoc] using
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε X R x

@[reassoc]
theorem homologyZeroPoint_naturality {X Y : SSet.{w}} (f : X ⟶ Y)
    (R : C) (x : X _⦋0⦌) :
    homologyZeroPoint X R x ≫ SSet.homologyMap f R 0 =
      homologyZeroPoint Y R (f.app _ x) := by
  dsimp only [homologyZeroPoint, SSet.homologyMap]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  simp

end SSet

namespace TopCat

universe u

open ContinuousMap

/-- The degree-zero homology class represented by a point. -/
noncomputable def singularHomologyZeroPoint (X : TopCat.{u}) (x : X) :
    singularHomologyIntegerCoefficients ⟶ (integralSingularHomologyFunctor 0).obj X :=
  show singularHomologyIntegerCoefficients ⟶
      (toSSet.obj X).homology singularHomologyIntegerCoefficients 0 from
    SSet.homologyZeroPoint (toSSet.obj X) singularHomologyIntegerCoefficients
      (toSSetObj₀Equiv.symm x)

@[reassoc]
theorem singularHomologyZeroPoint_homology₀Iso (X : TopCat.{u}) (x : X) :
    singularHomologyZeroPoint X x ≫
        (X.singularHomology₀Iso singularHomologyIntegerCoefficients).hom =
      Sigma.ι (fun _ : ZerothHomotopy X ↦ singularHomologyIntegerCoefficients)
        (.mk x) := by
  change SSet.homologyZeroPoint (toSSet.obj X) singularHomologyIntegerCoefficients
      (toSSetObj₀Equiv.symm x) ≫
      ((toSSet.obj X).homology₀Iso singularHomologyIntegerCoefficients ≪≫
        (sigmaConst.obj singularHomologyIntegerCoefficients).mapIso
          zerothHomotopyEquiv.toIso.symm).hom = _
  rw [Iso.trans_hom, ← Category.assoc]
  rw [SSet.homologyZeroPoint_homology₀Iso]
  simp

@[reassoc (attr := simp)]
theorem singularHomologyZeroPoint_augmentation (X : TopCat.{u}) (x : X) :
    singularHomologyZeroPoint X x ≫
        X.singularHomology₀ε singularHomologyIntegerCoefficients =
      𝟙 singularHomologyIntegerCoefficients := by
  change singularHomologyZeroPoint X x ≫
      (toSSet.obj X).homology₀ε singularHomologyIntegerCoefficients = _
  exact SSet.homologyZeroPoint_augmentation
    (toSSet.obj X) singularHomologyIntegerCoefficients
    (toSSetObj₀Equiv.symm x)

@[reassoc]
theorem singularHomologyZeroPoint_naturality {X Y : TopCat.{u}}
    (f : X ⟶ Y) (x : X) :
    singularHomologyZeroPoint X x ≫ (integralSingularHomologyFunctor 0).map f =
      singularHomologyZeroPoint Y (f x) := by
  change SSet.homologyZeroPoint (toSSet.obj X) singularHomologyIntegerCoefficients
      (toSSetObj₀Equiv.symm x) ≫
        SSet.homologyMap (toSSet.map f) singularHomologyIntegerCoefficients 0 = _
  rw [SSet.homologyZeroPoint_naturality]
  rfl

/-- The total degree-zero augmentation commutes with every continuous map. -/
@[reassoc]
theorem singularHomologyZeroAugmentation_naturality {X Y : TopCat.{u}}
    (f : X ⟶ Y) :
    (integralSingularHomologyFunctor 0).map f ≫
        Y.singularHomology₀ε singularHomologyIntegerCoefficients =
      X.singularHomology₀ε singularHomologyIntegerCoefficients := by
  rw [← cancel_epi (X.singularHomology₀Iso
    singularHomologyIntegerCoefficients).inv]
  apply Sigma.hom_ext
  intro c
  induction c using ZerothHomotopy.rec with
  | mk x =>
      rw [← singularHomologyZeroPoint_homology₀Iso X x]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [singularHomologyZeroPoint_naturality_assoc]
      simp

/-- Reduced integer singular homology in degree zero. -/
noncomputable abbrev reducedSingularHomologyZero (X : TopCat.{u}) : ModuleCat.{u, 0} ℤ :=
  kernel (X.singularHomology₀ε singularHomologyIntegerCoefficients)

/-- The canonical inclusion of reduced degree-zero homology into ordinary
degree-zero homology. -/
noncomputable abbrev reducedSingularHomologyZeroι (X : TopCat.{u}) :
    reducedSingularHomologyZero X ⟶ (integralSingularHomologyFunctor 0).obj X :=
  kernel.ι (X.singularHomology₀ε singularHomologyIntegerCoefficients)

/-- The map on reduced degree-zero homology induced by a continuous map. -/
noncomputable def reducedSingularHomologyZeroMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    reducedSingularHomologyZero X ⟶ reducedSingularHomologyZero Y :=
  kernel.map
    (X.singularHomology₀ε singularHomologyIntegerCoefficients)
    (Y.singularHomology₀ε singularHomologyIntegerCoefficients)
    ((integralSingularHomologyFunctor 0).map f)
    (𝟙 singularHomologyIntegerCoefficients)
    (by
      rw [Category.comp_id]
      exact (singularHomologyZeroAugmentation_naturality f).symm)

@[reassoc (attr := simp)]
theorem reducedSingularHomologyZeroMap_ι {X Y : TopCat.{u}} (f : X ⟶ Y) :
    reducedSingularHomologyZeroMap f ≫ reducedSingularHomologyZeroι Y =
      reducedSingularHomologyZeroι X ≫ (integralSingularHomologyFunctor 0).map f := by
  apply kernel.lift_ι

@[simp]
theorem reducedSingularHomologyZeroMap_id (X : TopCat.{u}) :
    reducedSingularHomologyZeroMap (𝟙 X) = 𝟙 (reducedSingularHomologyZero X) := by
  apply (cancel_mono (reducedSingularHomologyZeroι X)).1
  simp

@[reassoc]
theorem reducedSingularHomologyZeroMap_comp {X Y Z : TopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    reducedSingularHomologyZeroMap (f ≫ g) =
      reducedSingularHomologyZeroMap f ≫ reducedSingularHomologyZeroMap g := by
  apply (cancel_mono (reducedSingularHomologyZeroι Z)).1
  simp

/-- Reduced degree-zero singular homology is a functor. -/
@[simps]
noncomputable def reducedSingularHomologyZeroFunctor :
    TopCat.{u} ⥤ ModuleCat.{u, 0} ℤ where
  obj := reducedSingularHomologyZero
  map := reducedSingularHomologyZeroMap
  map_id := reducedSingularHomologyZeroMap_id
  map_comp := reducedSingularHomologyZeroMap_comp

/-- Nonnegative reduced singular homology.  Degree zero is the augmentation
kernel, and positive degrees are ordinary integer singular homology. -/
noncomputable def reducedSingularHomologyFunctor (n : ℕ) :
    TopCat.{u} ⥤ ModuleCat.{u, 0} ℤ :=
  match n with
  | 0 => reducedSingularHomologyZeroFunctor
  | n + 1 => integralSingularHomologyFunctor (n + 1)

/-- The object-level nonnegative reduced singular homology group. -/
noncomputable abbrev reducedSingularHomology (X : TopCat.{u}) (n : ℕ) :
    ModuleCat.{u, 0} ℤ :=
  (reducedSingularHomologyFunctor n).obj X

/-- The induced map on nonnegative reduced singular homology. -/
noncomputable abbrev reducedSingularHomologyMap {X Y : TopCat.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    reducedSingularHomology X n ⟶ reducedSingularHomology Y n :=
  (reducedSingularHomologyFunctor n).map f

/-- In degree zero, the nonnegative interface is the augmentation kernel. -/
noncomputable def reducedSingularHomologyZeroIso (X : TopCat.{u}) :
    reducedSingularHomology X 0 ≅ reducedSingularHomologyZero X :=
  eqToIso (by simp [reducedSingularHomology, reducedSingularHomologyFunctor])

/-- The canonical inclusion from the degree-zero nonnegative reduced-homology
interface into ordinary degree-zero integral singular homology. -/
noncomputable def reducedSingularHomologyZeroInclusion (X : TopCat.{u}) :
    reducedSingularHomology X 0 ⟶
      (integralSingularHomologyFunctor 0).obj X :=
  (reducedSingularHomologyZeroIso X).hom ≫
    reducedSingularHomologyZeroι X

instance reducedSingularHomologyZeroInclusion_mono (X : TopCat.{u}) :
    Mono (reducedSingularHomologyZeroInclusion X) := by
  dsimp [reducedSingularHomologyZeroInclusion]
  infer_instance

/-- The degree-zero reduced inclusion is natural for continuous maps. -/
@[reassoc]
theorem reducedSingularHomologyZeroInclusion_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    reducedSingularHomologyMap f 0 ≫
        reducedSingularHomologyZeroInclusion Y =
      reducedSingularHomologyZeroInclusion X ≫
        (integralSingularHomologyFunctor 0).map f := by
  change reducedSingularHomologyZeroMap f ≫
      reducedSingularHomologyZeroι Y =
    reducedSingularHomologyZeroι X ≫
      (integralSingularHomologyFunctor 0).map f
  exact reducedSingularHomologyZeroMap_ι f

/-- The degree-zero reduced inclusion with its codomain displayed using the
ordinary integral singular-homology abbreviation. -/
noncomputable def reducedSingularHomologyZeroToOrdinary (X : TopCat.{u}) :
    reducedSingularHomology X 0 ⟶ integralSingularHomology X 0 :=
  reducedSingularHomologyZeroInclusion X

instance reducedSingularHomologyZeroToOrdinary_mono (X : TopCat.{u}) :
    Mono (reducedSingularHomologyZeroToOrdinary X) := by
  change Mono (reducedSingularHomologyZeroInclusion X)
  infer_instance

/-- The reduced degree-zero inclusion is annihilated by augmentation. -/
@[reassoc (attr := simp)]
theorem reducedSingularHomologyZeroToOrdinary_augmentation (X : TopCat.{u}) :
    reducedSingularHomologyZeroToOrdinary X ≫
      X.singularHomology₀ε singularHomologyIntegerCoefficients = 0 := by
  exact kernel.condition _

/-- The reduced degree-zero inclusion is the kernel of augmentation. -/
noncomputable def reducedSingularHomologyZeroToOrdinaryIsKernel (X : TopCat.{u}) :
    IsLimit (KernelFork.ofι (reducedSingularHomologyZeroToOrdinary X)
      (reducedSingularHomologyZeroToOrdinary_augmentation X)) := by
  exact kernelIsKernel _

/-- Reduced integral degree-zero homology is the coproduct of the integer
coefficient object over path components other than that of `x`. The comparison
is the uniqueness isomorphism between two kernels of the same augmentation.

For the reduced-homology background see J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §§1 and 3. This construction uses Mathlib's ordinary singular
homology (Joël Riou) and the project's augmentation-kernel model, not a
comparison with May's based-relative theory. -/
noncomputable def reducedSingularHomologyZeroComponentsIso (X : TopCat.{u}) (x : X) :
    reducedSingularHomology X 0 ≅
      ∐ (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦
        singularHomologyIntegerCoefficients) :=
  (reducedSingularHomologyZeroToOrdinaryIsKernel X).conePointUniqueUpToIso
    (singularHomologyZeroComponentInclusionIsKernel X
      singularHomologyIntegerCoefficients x)

/-- The inverse component presentation agrees with the component inclusion
when followed by the reduced-to-ordinary map. -/
@[reassoc]
theorem reducedSingularHomologyZeroComponentsIso_inv_toOrdinary
    (X : TopCat.{u}) (x : X) :
    (reducedSingularHomologyZeroComponentsIso X x).inv ≫
        reducedSingularHomologyZeroToOrdinary X =
      singularHomologyZeroComponentInclusion X singularHomologyIntegerCoefficients x := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp
    (reducedSingularHomologyZeroToOrdinaryIsKernel X)
    (singularHomologyZeroComponentInclusionIsKernel X
      singularHomologyIntegerCoefficients x) WalkingParallelPair.zero

/-- The ordinary image of a reduced component generator is its component
injection minus the basepoint-component injection under Mathlib's `H₀` isomorphism. -/
@[reassoc]
theorem ι_reducedSingularHomologyZeroComponentsIso_inv_toOrdinary
    (X : TopCat.{u}) (x : X)
    (c : {c : ZerothHomotopy X // c ≠ .mk x}) :
    Sigma.ι (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦
        singularHomologyIntegerCoefficients) c ≫
        (reducedSingularHomologyZeroComponentsIso X x).inv ≫
        reducedSingularHomologyZeroToOrdinary X =
      (Sigma.ι (fun _ : ZerothHomotopy X ↦ singularHomologyIntegerCoefficients) c.val -
        Sigma.ι (fun _ : ZerothHomotopy X ↦ singularHomologyIntegerCoefficients) (.mk x)) ≫
          (X.singularHomology₀Iso singularHomologyIntegerCoefficients).inv := by
  rw [reducedSingularHomologyZeroComponentsIso_inv_toOrdinary]
  exact ι_singularHomologyZeroComponentInclusion X singularHomologyIntegerCoefficients x c

/-- For a point `y` outside the basepoint path component, the corresponding
reduced generator has ordinary image `[y] - [x]`, using the existing point classes. -/
@[reassoc]
theorem ι_reducedSingularHomologyZeroComponentsIso_inv_toOrdinary_point
    (X : TopCat.{u}) (x y : X) (h : ZerothHomotopy.mk y ≠ .mk x) :
    Sigma.ι (fun _ : {c : ZerothHomotopy X // c ≠ .mk x} ↦
        singularHomologyIntegerCoefficients) ⟨.mk y, h⟩ ≫
        (reducedSingularHomologyZeroComponentsIso X x).inv ≫
        reducedSingularHomologyZeroToOrdinary X =
      singularHomologyZeroPoint X y - singularHomologyZeroPoint X x := by
  rw [ι_reducedSingularHomologyZeroComponentsIso_inv_toOrdinary]
  apply (Iso.comp_inv_eq
    (X.singularHomology₀Iso singularHomologyIntegerCoefficients)).2
  rw [Preadditive.sub_comp, singularHomologyZeroPoint_homology₀Iso,
    singularHomologyZeroPoint_homology₀Iso]

/-- Naturality of the degree-zero reduced inclusion, with ordinary homology
displayed explicitly. -/
@[reassoc]
theorem reducedSingularHomologyZeroToOrdinary_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) :
    reducedSingularHomologyMap f 0 ≫
        reducedSingularHomologyZeroToOrdinary Y =
      reducedSingularHomologyZeroToOrdinary X ≫
        HomologicalComplex.homologyMap (integralSingularChainMap f) 0 := by
  exact reducedSingularHomologyZeroInclusion_naturality f

/-- In every positive degree, reduced and ordinary integer singular homology
are canonically identical. -/
noncomputable def reducedSingularHomologyIsoOfNeZero (X : TopCat.{u}) (n : ℕ)
    (hn : n ≠ 0) :
    reducedSingularHomology X n ≅ integralSingularHomology X n :=
  match n with
  | 0 => (hn rfl).elim
  | _ + 1 => Iso.refl _

@[reassoc]
theorem reducedSingularHomologyMap_isoOfNeZero {X Y : TopCat.{u}}
    (f : X ⟶ Y) (n : ℕ) (hn : n ≠ 0) :
    reducedSingularHomologyMap f n ≫
        (reducedSingularHomologyIsoOfNeZero Y n hn).hom =
      (reducedSingularHomologyIsoOfNeZero X n hn).hom ≫
      HomologicalComplex.homologyMap (integralSingularChainMap f) n := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => rfl

/-- Homotopic maps induce the same map on reduced degree-zero homology. -/
theorem reducedSingularHomologyZeroMap_eq_of_homotopy {X Y : TopCat.{u}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    reducedSingularHomologyZeroMap f = reducedSingularHomologyZeroMap g := by
  apply (cancel_mono (reducedSingularHomologyZeroι Y)).1
  simp only [reducedSingularHomologyZeroMap_ι]
  have h := H.congr_homologyMap_singularChainComplexFunctor
    singularHomologyIntegerCoefficients 0
  change reducedSingularHomologyZeroι X ≫
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{u, 0} ℤ)).obj
          singularHomologyIntegerCoefficients).map f) 0 =
    reducedSingularHomologyZeroι X ≫
      HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{u, 0} ℤ)).obj
          singularHomologyIntegerCoefficients).map g) 0
  rw [h]

/-- Homotopic maps induce the same map on reduced integer singular homology in
every nonnegative degree. -/
theorem reducedSingularHomologyMap_eq_of_homotopy {X Y : TopCat.{u}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    reducedSingularHomologyMap f n = reducedSingularHomologyMap g n := by
  cases n with
  | zero => exact reducedSingularHomologyZeroMap_eq_of_homotopy H
  | succ n =>
      exact H.congr_homologyMap_singularChainComplexFunctor
        singularHomologyIntegerCoefficients (n + 1)

/-- A homotopy equivalence induces an isomorphism on reduced integer singular
homology in every nonnegative degree.

For the reduced-homology background see J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §§1 and 3. This construction uses Mathlib's ordinary singular
homology (Joël Riou) and the project's augmentation-kernel model, not a
comparison with May's based-relative theory. -/
noncomputable def reducedSingularHomologyIsoOfHomotopyEquiv
    {X Y : TopCat.{u}} (e : (X : Type u) ≃ₕ (Y : Type u)) (n : ℕ) :
    reducedSingularHomology X n ≅ reducedSingularHomology Y n where
  hom := reducedSingularHomologyMap (TopCat.ofHom e.toFun) n
  inv := reducedSingularHomologyMap (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    change reducedSingularHomologyMap
      (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) n = _
    rw [reducedSingularHomologyMap_eq_of_homotopy H n]
    exact (reducedSingularHomologyFunctor n).map_id X
  inv_hom_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    change reducedSingularHomologyMap
      (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) n = _
    rw [reducedSingularHomologyMap_eq_of_homotopy H n]
    exact (reducedSingularHomologyFunctor n).map_id Y

/-- A path-connected space has zero reduced degree-zero integer homology. -/
theorem isZero_reducedSingularHomologyZero_of_pathConnected (X : TopCat.{u})
    [PathConnectedSpace X] :
    IsZero (reducedSingularHomologyZero X) :=
  isZero_kernel_of_mono
    (X.singularHomology₀ε singularHomologyIntegerCoefficients)

/-- In particular, a contractible space has zero reduced degree-zero integer
homology.  A `ContractibleSpace` instance includes nonemptiness. -/
theorem isZero_reducedSingularHomologyZero_of_contractible (X : TopCat.{u})
    [ContractibleSpace (X : Type u)] :
    IsZero (reducedSingularHomologyZero X) :=
  isZero_reducedSingularHomologyZero_of_pathConnected X

/-- The canonical one-point space, lifted into an arbitrary universe. -/
abbrev onePointSpace.{v} : TopCat.{v} := TopCat.of (ULift.{v} PUnit)

/-- Reduced integer singular homology of a point vanishes in every
nonnegative degree. -/
theorem isZero_reducedSingularHomology_onePoint (n : ℕ) :
    IsZero (reducedSingularHomology onePointSpace.{u} n) := by
  cases n with
  | zero =>
      exact isZero_reducedSingularHomologyZero_of_pathConnected onePointSpace.{u}
  | succ n =>
      change IsZero
        (((singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj
          singularHomologyIntegerCoefficients).obj onePointSpace.{u})
      exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat.{u} ℤ) (n + 1) singularHomologyIntegerCoefficients onePointSpace.{u}
        (Nat.succ_ne_zero n)

/-- Every contractible space has zero reduced integer singular homology in
every nonnegative degree. This statement preserves the universe of the
ambient space.

For the reduced-homology background see J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §§1 and 3. This construction uses Mathlib's ordinary singular
homology (Joël Riou) and the project's augmentation-kernel model, not a
comparison with May's based-relative theory. -/
theorem isZero_reducedSingularHomology_of_contractible (X : TopCat.{u})
    [ContractibleSpace (X : Type u)] (n : ℕ) :
    IsZero (reducedSingularHomology X n) := by
  let e := Classical.choice
    (ContractibleSpace.hequiv (X : Type u) (ULift.{u} PUnit))
  exact (isZero_reducedSingularHomology_onePoint n).of_iso
    (reducedSingularHomologyIsoOfHomotopyEquiv e n)

/-- The canonical empty space, lifted into an arbitrary universe. -/
abbrev emptySpace.{v} : TopCat.{v} := TopCat.of (ULift.{v} Empty)

/-- Under the nonnegative convention of this file, reduced degree-zero
homology of the empty space is zero: its ordinary `H₀` is already zero. -/
theorem isZero_reducedSingularHomologyZero_empty :
    IsZero (reducedSingularHomologyZero emptySpace.{u}) := by
  have hEmpty (c : ZerothHomotopy emptySpace.{u}) : False := by
    induction c using ZerothHomotopy.rec with
    | mk x => exact x.down.elim
  have hCoprod : IsZero
      (∐ (fun _ : ZerothHomotopy emptySpace.{u} ↦
        singularHomologyIntegerCoefficients)) := by
    apply IsColimit.isZero_pt (coproductIsCoproduct _)
    apply Functor.isZero
    intro j
    exact (hEmpty j.as).elim
  have hH₀ : IsZero
      ((integralSingularHomologyFunctor 0).obj emptySpace.{u}) :=
    hCoprod.of_iso (emptySpace.{u}.singularHomology₀Iso
      singularHomologyIntegerCoefficients)
  exact hH₀.of_mono (reducedSingularHomologyZeroι emptySpace.{u})

/-! ## The discrete two-point space -/

/-- The canonical discrete two-point space used below. -/
abbrev twoPointSpace : TopCat := TopCat.of Bool

/-- Transposition of the canonical discrete two-point space. -/
def twoPointSwap : twoPointSpace ⟶ twoPointSpace :=
  TopCat.ofHom ⟨Bool.not, continuous_of_discreteTopology⟩

@[simp]
theorem twoPointSwap_apply (b : Bool) : twoPointSwap b = !b := rfl

/-- On a totally disconnected space every path has equal endpoints. -/
theorem path_endpoints_eq_of_totallyDisconnected
    {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    {x y : X} (p : Path x y) : x = y := by
  simpa using
    TotallyDisconnectedSpace.eq_of_continuous p p.continuous (0 : Set.Icc (0 : ℝ) 1) 1

/-- Path components of the discrete two-point space, with no choice of
representatives: the component of `b` is sent to `b`. -/
noncomputable def twoPointZerothHomotopyEquiv :
    ZerothHomotopy twoPointSpace ≃ Bool where
  toFun := ZerothHomotopy.lift id
    (fun {_ _} p ↦ path_endpoints_eq_of_totallyDisconnected p)
  invFun := ZerothHomotopy.mk
  left_inv c := by induction c using ZerothHomotopy.rec; rfl
  right_inv _ := rfl

@[simp]
theorem twoPointZerothHomotopyEquiv_mk (b : Bool) :
    twoPointZerothHomotopyEquiv (.mk b) = b := rfl

/-- The canonical presentation of `H₀` of the two-point space by the two
point classes, ordered as `false`, `true`. -/
noncomputable def twoPointSingularHomologyZeroIso :
    (integralSingularHomologyFunctor 0).obj twoPointSpace ≅
      ∐ (fun _ : Bool ↦ singularHomologyIntegerCoefficients) :=
  twoPointSpace.singularHomology₀Iso singularHomologyIntegerCoefficients ≪≫
    (sigmaConst.obj singularHomologyIntegerCoefficients).mapIso
      twoPointZerothHomotopyEquiv.toIso

@[reassoc]
theorem singularHomologyZeroPoint_twoPoint_iso (b : Bool) :
    singularHomologyZeroPoint twoPointSpace b ≫
        twoPointSingularHomologyZeroIso.hom =
      Sigma.ι (fun _ : Bool ↦ singularHomologyIntegerCoefficients) b := by
  rw [twoPointSingularHomologyZeroIso, Iso.trans_hom, ← Category.assoc]
  rw [singularHomologyZeroPoint_homology₀Iso]
  change Sigma.ι (fun _ : ZerothHomotopy twoPointSpace ↦
      singularHomologyIntegerCoefficients) (.mk b) ≫
      Sigma.map' (fun c ↦ twoPointZerothHomotopyEquiv c)
        (fun _ ↦ 𝟙 singularHomologyIntegerCoefficients) =
    Sigma.ι (fun _ : Bool ↦ singularHomologyIntegerCoefficients) b
  rw [Sigma.ι_comp_map', Category.id_comp]
  rw [twoPointZerothHomotopyEquiv_mk]

@[reassoc]
theorem twoPoint_sigmaι_iso_inv (b : Bool) :
    Sigma.ι (fun _ : Bool ↦ singularHomologyIntegerCoefficients) b ≫
        twoPointSingularHomologyZeroIso.inv =
      singularHomologyZeroPoint twoPointSpace b := by
  rw [← singularHomologyZeroPoint_twoPoint_iso b]
  simp

@[reassoc]
theorem twoPointSingularHomologyZeroIso_hom_desc :
    twoPointSingularHomologyZeroIso.hom ≫
        Sigma.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) =
      twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients := by
  rw [← cancel_epi twoPointSingularHomologyZeroIso.inv]
  apply Sigma.hom_ext
  intro b
  simp only [Iso.inv_hom_id_assoc, Sigma.ι_desc]
  rw [twoPoint_sigmaι_iso_inv_assoc]
  simp

/-- The chosen reduced `H₀` basis class is `[false] - [true]`.  This fixes the
sign used by the two-point computation and all naturality statements below. -/
noncomputable def twoPointReducedBasisClass :
    singularHomologyIntegerCoefficients ⟶
      (integralSingularHomologyFunctor 0).obj twoPointSpace :=
  singularHomologyZeroPoint twoPointSpace false -
    singularHomologyZeroPoint twoPointSpace true

@[reassoc (attr := simp)]
theorem twoPointReducedBasisClass_augmentation :
    twoPointReducedBasisClass ≫
        twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients = 0 := by
  simp [twoPointReducedBasisClass, Preadditive.sub_comp]

/-- The basis vector `1 ↦ [false] - [true]` in reduced `H₀`. -/
noncomputable def twoPointReducedBasis :
    singularHomologyIntegerCoefficients ⟶ reducedSingularHomologyZero twoPointSpace :=
  kernel.lift
    (twoPointSpace.singularHomology₀ε singularHomologyIntegerCoefficients)
    twoPointReducedBasisClass twoPointReducedBasisClass_augmentation

@[reassoc (attr := simp)]
theorem twoPointReducedBasis_ι :
    twoPointReducedBasis ≫ reducedSingularHomologyZeroι twoPointSpace =
      twoPointReducedBasisClass := by
  apply kernel.lift_ι

/-- The `false` coordinate on reduced `H₀`, after the ordered two-point
presentation and its canonical finite biproduct structure. -/
noncomputable def twoPointReducedCoordinate :
    reducedSingularHomologyZero twoPointSpace ⟶ singularHomologyIntegerCoefficients :=
  reducedSingularHomologyZeroι twoPointSpace ≫
    twoPointSingularHomologyZeroIso.hom ≫
    (biproduct.isoCoproduct
      (fun _ : Bool ↦ singularHomologyIntegerCoefficients)).inv ≫
    biproduct.π (fun _ : Bool ↦ singularHomologyIntegerCoefficients) false

@[reassoc]
theorem twoPointReducedBasis_coordinate :
    twoPointReducedBasis ≫ twoPointReducedCoordinate =
      𝟙 singularHomologyIntegerCoefficients := by
  simp only [twoPointReducedCoordinate, twoPointReducedBasis_ι_assoc,
    twoPointReducedBasisClass, Preadditive.sub_comp]
  rw [singularHomologyZeroPoint_twoPoint_iso_assoc,
    singularHomologyZeroPoint_twoPoint_iso_assoc]
  simp [biproduct.isoCoproduct_inv]

theorem twoPointReducedCoordinate_basis :
    twoPointReducedCoordinate ≫ twoPointReducedBasis =
      𝟙 (reducedSingularHomologyZero twoPointSpace) := by
  let P : Bool → ModuleCat ℤ :=
    fun _ ↦ singularHomologyIntegerCoefficients
  have hdesc :
      (biproduct.isoCoproduct P).inv ≫
          biproduct.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) =
        Sigma.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) := by
    rw [biproduct.isoCoproduct_inv]
    apply Sigma.hom_ext
    intro b
    simp [P]
  have hbool :
      biproduct.π P false + biproduct.π P true =
        biproduct.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) := by
    apply biproduct.hom_ext'
    intro b
    cases b <;> simp [P, Preadditive.comp_add]
  have hdesc' :
      twoPointSingularHomologyZeroIso.hom ≫
          (biproduct.isoCoproduct P).inv ≫
          biproduct.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) =
        twoPointSingularHomologyZeroIso.hom ≫
          Sigma.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) := by
    rw [hdesc]
  have hdesc'' :
      reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          (biproduct.isoCoproduct P).inv ≫
          biproduct.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) =
        reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          Sigma.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) :=
    congrArg (reducedSingularHomologyZeroι twoPointSpace ≫ ·) hdesc'
  have haug :
      reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          Sigma.desc (fun _ : Bool ↦ 𝟙 singularHomologyIntegerCoefficients) = 0 := by
    simp only [twoPointSingularHomologyZeroIso_hom_desc,
      kernel.condition]
  have hsum :
      (reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          (biproduct.isoCoproduct P).inv ≫ biproduct.π P false) +
        (reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          (biproduct.isoCoproduct P).inv ≫ biproduct.π P true) = 0 := by
    rw [← Preadditive.comp_add, ← Preadditive.comp_add,
      ← Preadditive.comp_add, hbool]
    exact hdesc''.trans haug
  have htrue :
      reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          (biproduct.isoCoproduct P).inv ≫ biproduct.π P true =
        -(reducedSingularHomologyZeroι twoPointSpace ≫
          twoPointSingularHomologyZeroIso.hom ≫
          (biproduct.isoCoproduct P).inv ≫ biproduct.π P false) :=
    eq_neg_of_add_eq_zero_right hsum
  apply (cancel_mono (reducedSingularHomologyZeroι twoPointSpace)).1
  simp only [Category.assoc, twoPointReducedBasis_ι, Category.id_comp]
  apply (cancel_mono (twoPointSingularHomologyZeroIso.hom ≫
    (biproduct.isoCoproduct P).inv)).1
  apply biproduct.hom_ext
  intro b
  cases b with
  | false =>
      simp [twoPointReducedCoordinate, twoPointReducedBasisClass, P,
        Preadditive.comp_sub, biproduct.isoCoproduct_inv,
        singularHomologyZeroPoint_twoPoint_iso_assoc]
  | true =>
      simpa [twoPointReducedCoordinate, twoPointReducedBasisClass, P,
        Preadditive.comp_sub, biproduct.isoCoproduct_inv,
        singularHomologyZeroPoint_twoPoint_iso_assoc] using htrue.symm

/-- The explicit two-point computation with basis `[false] - [true]`.

For the reduced-homology background see J. Peter May, *A Concise Course in Algebraic Topology*,
Chapter 14, §§1 and 3. This construction uses Mathlib's ordinary singular
homology (Joël Riou) and the project's augmentation-kernel model, not a
comparison with May's based-relative theory. -/
noncomputable def reducedSingularHomologyZeroTwoPointIso :
    reducedSingularHomologyZero twoPointSpace ≅
      singularHomologyIntegerCoefficients where
  hom := twoPointReducedCoordinate
  inv := twoPointReducedBasis
  hom_inv_id := twoPointReducedCoordinate_basis
  inv_hom_id := twoPointReducedBasis_coordinate

/-- The universe-zero coefficient object is canonically the ordinary integer
module. -/
def singularHomologyIntegerCoefficientsIso :
    singularHomologyIntegerCoefficients.{0} ≅ ModuleCat.of ℤ ℤ :=
  ULift.moduleEquiv.toModuleIso

/-- The two-point computation stated with the unlifted integer module as its
target. -/
noncomputable def reducedSingularHomologyZeroTwoPointIntegerIso :
    reducedSingularHomologyZero twoPointSpace ≅ ModuleCat.of ℤ ℤ :=
  reducedSingularHomologyZeroTwoPointIso ≪≫
    singularHomologyIntegerCoefficientsIso

/-- Transposition sends the chosen basis `[false] - [true]` to its negative. -/
@[reassoc]
theorem twoPointReducedBasis_swap :
    twoPointReducedBasis ≫ reducedSingularHomologyZeroMap twoPointSwap =
      -twoPointReducedBasis := by
  apply (cancel_mono (reducedSingularHomologyZeroι twoPointSpace)).1
  rw [Category.assoc, reducedSingularHomologyZeroMap_ι]
  rw [← Category.assoc, twoPointReducedBasis_ι]
  rw [Preadditive.neg_comp, twoPointReducedBasis_ι]
  simp only [twoPointReducedBasisClass, Preadditive.sub_comp]
  rw [singularHomologyZeroPoint_naturality,
    singularHomologyZeroPoint_naturality]
  simp [twoPointSwap]

/-- In the basis `[false] - [true]`, transposition acts on reduced `H₀` by
multiplication by `-1`. -/
theorem reducedSingularHomologyZeroTwoPointIso_swap :
    reducedSingularHomologyZeroTwoPointIso.inv ≫
        reducedSingularHomologyZeroMap twoPointSwap ≫
        reducedSingularHomologyZeroTwoPointIso.hom =
      -(𝟙 singularHomologyIntegerCoefficients) := by
  change twoPointReducedBasis ≫
      reducedSingularHomologyZeroMap twoPointSwap ≫
      twoPointReducedCoordinate = -(𝟙 singularHomologyIntegerCoefficients)
  rw [← Category.assoc, twoPointReducedBasis_swap]
  rw [Preadditive.neg_comp, twoPointReducedBasis_coordinate]

/-- The unlifted-integer form of the transposition computation: conjugating by
`reducedSingularHomologyZeroTwoPointIntegerIso` gives `-𝟙` on `ℤ`. -/
theorem reducedSingularHomologyZeroTwoPointIntegerIso_swap :
    reducedSingularHomologyZeroTwoPointIntegerIso.inv ≫
        reducedSingularHomologyZeroMap twoPointSwap ≫
        reducedSingularHomologyZeroTwoPointIntegerIso.hom =
      -(𝟙 (ModuleCat.of ℤ ℤ)) := by
  change singularHomologyIntegerCoefficientsIso.inv ≫
      twoPointReducedBasis ≫ reducedSingularHomologyZeroMap twoPointSwap ≫
      twoPointReducedCoordinate ≫ singularHomologyIntegerCoefficientsIso.hom =
    -(𝟙 (ModuleCat.of ℤ ℤ))
  rw [twoPointReducedBasis_swap_assoc]
  rw [Preadditive.neg_comp, twoPointReducedBasis_coordinate_assoc]
  simp

/-- The identity map acts as the identity in the same ordered basis. -/
theorem reducedSingularHomologyZeroTwoPointIso_id :
    reducedSingularHomologyZeroTwoPointIso.inv ≫
        reducedSingularHomologyZeroMap (𝟙 twoPointSpace) ≫
        reducedSingularHomologyZeroTwoPointIso.hom =
      𝟙 singularHomologyIntegerCoefficients := by
  simp

end TopCat
