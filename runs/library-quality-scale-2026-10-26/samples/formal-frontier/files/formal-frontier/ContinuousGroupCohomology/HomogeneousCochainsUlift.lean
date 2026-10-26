/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.TopRepUlift
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Universe lifts of homogeneous continuous cochains

This file compares the continuous-function coinduction, invariants, recursive
coinduced resolution, and homogeneous cochain complex of a topological
representation with the corresponding constructions after `ULift`.

The continuous-function, coinduction, and invariants comparisons allow
independently chosen lift universes. Mathlib's current recursive resolution and
homogeneous-cochain API places the group and coefficient carrier in one small
universe, so the final resolution and complex isomorphisms deliberately use
the same lift universe on both sides.
-/

set_option warningAsError true

@[expose] public section

universe u v w v' w'

open CategoryTheory ContinuousMap

namespace ContinuousMap

variable {k : Type u} [Semiring k] [TopologicalSpace k]
variable {G : Type v} [TopologicalSpace G]
variable {M : Type w} [TopologicalSpace M] [AddCommMonoid M] [Module k M]
  [ContinuousAdd M] [ContinuousSMul k M]

/-- Raising a continuous-function space is continuously linearly equivalent to
the continuous-function space between independently raised source and target
types. -/
noncomputable def uliftContinuousLinearEquiv :
    ULift.{max v' w'} C(G, M) ≃L[k] C(ULift.{v'} G, ULift.{w'} M) :=
  let downG : C(ULift.{v'} G, G) := ⟨ULift.down, continuous_uliftDown⟩
  let upG : C(G, ULift.{v'} G) := ⟨ULift.up, continuous_uliftUp⟩
  let downM : C(ULift.{w'} M, M) := ⟨ULift.down, continuous_uliftDown⟩
  let upM : C(M, ULift.{w'} M) := ⟨ULift.up, continuous_uliftUp⟩
  let eMaps : ULift.{max v' w'} C(G, M) ≃L[k] C(G, M) :=
    ContinuousLinearEquiv.ulift
  ContinuousLinearEquiv.mk
    { toFun := fun F =>
        upM.comp (F.down.comp downG)
      invFun := fun F =>
        ULift.up (downM.comp (F.comp upG))
      left_inv := fun F => by ext x; simp [downG, upG, downM, upM]
      right_inv := fun F => by ext x; simp [downG, upG, downM, upM]
      map_add' := fun F H => by ext x; simp [downG, upM]
      map_smul' := fun r F => by ext x; simp [downG, upM] }
    (by
      change Continuous (fun F : ULift.{max v' w'} C(G, M) =>
        upM.comp (F.down.comp downG))
      exact (continuous_postcomp upM).comp
        ((continuous_precomp downG).comp eMaps.continuous))
    (by
      change Continuous (fun F : C(ULift.{v'} G, ULift.{w'} M) =>
        ULift.up (downM.comp (F.comp upG)))
      exact eMaps.symm.continuous.comp
        ((continuous_postcomp downM).comp (continuous_precomp upG)))

end ContinuousMap

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Coinduction by continuous functions commutes with independently raising
the acting group and coefficient carrier. -/
noncomputable def coind₁UliftEquiv (X : TopRep.{w} k G) :
    (TopRep.ulift.{u, v, v', max v w, max v' w'} X.coind₁).ρ.Equiv
      (TopRep.ulift.{u, v, v', w, w'} X).coind₁.ρ :=
  ContRepresentation.Equiv.mk
    (ContinuousMap.uliftContinuousLinearEquiv
      (k := k) (G := G) (M := X))
    (fun g => by
      ext F x
      rfl)

/-- The topological representations obtained by coinducing before or after
independent universe lifts are isomorphic. -/
noncomputable def coind₁UliftIso (X : TopRep.{w} k G) :
    TopRep.ulift.{u, v, v', max v w, max v' w'} X.coind₁ ≅
      (TopRep.ulift.{u, v, v', w, w'} X).coind₁ where
  hom := TopRep.ofHom (coind₁UliftEquiv X).toContIntertwiningMap
  inv := TopRep.ofHom (coind₁UliftEquiv X).symm.toContIntertwiningMap
  hom_inv_id := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro F
    exact (coind₁UliftEquiv X).symm_apply_apply F
  inv_hom_id := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro F
    exact (coind₁UliftEquiv X).apply_symm_apply F

private lemma uliftMap_coind₁ι_comp_coind₁UliftIso (X : TopRep.{v} k G) :
    TopRep.uliftMap.{u, v, v, v, v} (TopRep.ofHom X.ρ.coind₁ι) ≫
        (coind₁UliftIso.{u, v, v, v, v} X).hom =
      TopRep.ofHom (TopRep.ulift.{u, v, v, v, v} X).ρ.coind₁ι := by
  ext x g
  rfl

private lemma uliftMap_coind₁Map_comp_coind₁UliftIso
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) :
    TopRep.uliftMap.{u, v, v, v, v}
          (TopRep.ofHom (ContRepresentation.coind₁Map f.hom)) ≫
        (coind₁UliftIso.{u, v, v, v, v} Y).hom =
      (coind₁UliftIso.{u, v, v, v, v} X).hom ≫
        TopRep.ofHom (ContRepresentation.coind₁Map
          (TopRep.uliftMap.{u, v, v, v, v} f).hom) := by
  ext x g
  rfl

private lemma coind₁Map_comp {X Y Z : TopRep.{v} k (ULift.{v} G)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopRep.ofHom (ContRepresentation.coind₁Map f.hom) ≫
        TopRep.ofHom (ContRepresentation.coind₁Map g.hom) =
      TopRep.ofHom (ContRepresentation.coind₁Map (f ≫ g).hom) := by
  ext x h
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private lemma uliftMap_sub {X Y : TopRep.{v} k G} (f g : X ⟶ Y) :
    TopRep.uliftMap.{u, v, v, v, v} (f - g) =
      TopRep.uliftMap.{u, v, v, v, v} f -
        TopRep.uliftMap.{u, v, v, v, v} g := by
  ext x
  rfl

/-- Invariants commute with independently raising the acting group and
coefficient carrier. -/
noncomputable def invariantsUliftContinuousLinearEquiv (X : TopRep.{w} k G) :
    ULift.{w'} X.ρ.invariants ≃L[k]
      (TopRep.ulift.{u, v, v', w, w'} X).ρ.invariants :=
  ContinuousLinearEquiv.mk
    { toFun := fun x =>
        ⟨ULift.up x.down.1, fun g => by
          change ULift.up (X.ρ g.down x.down.1) = ULift.up x.down.1
          rw [x.down.2 g.down]⟩
      invFun := fun x =>
        ULift.up ⟨x.1.down, fun g => by
          exact congrArg ULift.down (x.2 (ULift.up g))⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl
      map_smul' := fun r x => by ext; rfl }
    (by
      exact (continuous_uliftUp.comp
        (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _)
    (by
      apply continuous_uliftUp.comp
      apply Continuous.subtype_mk
      exact continuous_uliftDown.comp continuous_subtype_val)

/-- The invariant topological modules before and after independent universe
lifts are isomorphic. -/
noncomputable def invariantsUliftIso (X : TopRep.{w} k G) :
    (TopModuleCat.uliftFunctor.{w', w} k).obj X.invariants ≅
      (TopRep.ulift.{u, v, v', w, w'} X).invariants :=
  TopModuleCat.ofIso (invariantsUliftContinuousLinearEquiv X)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private lemma invariantsUliftIso_naturality
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) :
    (TopModuleCat.uliftFunctor.{v, v} k).map
          (TopModuleCat.ofHom f.hom.mapInvariants) ≫
        (invariantsUliftIso.{u, v, v, v, v} Y).hom =
      (invariantsUliftIso.{u, v, v, v, v} X).hom ≫
        TopModuleCat.ofHom
          (TopRep.uliftMap.{u, v, v, v, v} f).hom.mapInvariants := by
  ext x
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private lemma invariantsMap_comp {X Y Z : TopRep.{v} k (ULift.{v} G)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopModuleCat.ofHom f.hom.mapInvariants ≫
        TopModuleCat.ofHom g.hom.mapInvariants =
      TopModuleCat.ofHom (f ≫ g).hom.mapInvariants := by
  ext x
  rfl

/-- In one common small universe, every term of the recursive coinduced
resolution is isomorphic to the corresponding term after raising the acting
group and coefficient carrier. -/
noncomputable def resolutionUliftIsoSameUniverse (X : TopRep.{v} k G) :
    (n : ℕ) →
      TopRep.ulift.{u, v, v, v, v} (X.resolutionX n) ≅
        (TopRep.ulift.{u, v, v, v, v} X).resolutionX n
  | 0 => Iso.refl _
  | n + 1 =>
      coind₁UliftIso.{u, v, v, v, v} (X.resolutionX n) ≪≫
        (coind₁Functor k (ULift.{v} G)).mapIso
          (resolutionUliftIsoSameUniverse X n)

/-- The termwise same-universe resolution isomorphisms are natural in the
coefficient representation. -/
lemma resolutionUliftIsoSameUniverse_naturality
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) (n : ℕ) :
    TopRep.uliftMap.{u, v, v, v, v}
          (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n) ≫
        (resolutionUliftIsoSameUniverse Y n).hom =
      (resolutionUliftIsoSameUniverse X n).hom ≫
        ContinuousCohomology.resolutionMap
          (ContinuousMonoidHom.id (ULift.{v} G))
          (TopRep.uliftMap.{u, v, v, v, v} f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [resolutionUliftIsoSameUniverse, Iso.trans_hom, Functor.mapIso_hom]
      ext F g
      exact congrArg (fun q => q.hom (ULift.up (F.down g.down))) ih

/-- The termwise same-universe resolution isomorphisms commute with the
recursive resolution differential. -/
lemma resolutionUliftIsoSameUniverse_d_comm
    (X : TopRep.{v} k G) (n : ℕ) :
    TopRep.uliftMap.{u, v, v, v, v} (TopRep.d X n) ≫
        (resolutionUliftIsoSameUniverse X (n + 1)).hom =
      (resolutionUliftIsoSameUniverse X n).hom ≫
        TopRep.d (TopRep.ulift.{u, v, v, v, v} X) n := by
  induction n with
  | zero =>
      ext x g
      rfl
  | succ n ih =>
      have ih' := ih
      simp only [resolutionUliftIsoSameUniverse, Iso.trans_hom,
        Functor.mapIso_hom] at ih'
      rw [TopRep.d_succ, TopRep.d_succ, uliftMap_sub]
      rw [Preadditive.sub_comp, Preadditive.comp_sub]
      simp only [resolutionUliftIsoSameUniverse,
        Iso.trans_hom, Functor.mapIso_hom]
      congr 1
      rw [← Category.assoc, uliftMap_coind₁Map_comp_coind₁UliftIso]
      rw [Category.assoc, coind₁Map_comp, ih', ← coind₁Map_comp,
        ← Category.assoc]

/-- Degreewise isomorphism between the raised homogeneous cochains and the
homogeneous cochains of the raised representation, in one small universe. -/
noncomputable def homogeneousCochainsUliftXIsoSameUniverse
    (X : TopRep.{v} k G) (n : ℕ) :
    (TopModuleCat.uliftFunctor.{v, v} k).obj (X.homogeneousCochains.X n) ≅
      (TopRep.ulift.{u, v, v, v, v} X).homogeneousCochains.X n :=
  invariantsUliftIso.{u, v, v, v, v} (X.resolutionX (n + 1)) ≪≫
    (invariantsFunctor k (ULift.{v} G)).mapIso
      (resolutionUliftIsoSameUniverse X (n + 1))

/-- The degreewise same-universe homogeneous-cochain isomorphisms commute with
the cochain differential. -/
lemma homogeneousCochainsUliftXIsoSameUniverse_comm
    (X : TopRep.{v} k G) (n : ℕ) :
    (TopModuleCat.uliftFunctor.{v, v} k).map
          ((TopRep.homogeneousCochains X).d n (n + 1)) ≫
        (homogeneousCochainsUliftXIsoSameUniverse X (n + 1)).hom =
      (homogeneousCochainsUliftXIsoSameUniverse X n).hom ≫
        (TopRep.homogeneousCochains
          (TopRep.ulift.{u, v, v, v, v} X)).d n (n + 1) := by
  rw [TopRep.homogeneousCochains.d_eq,
    TopRep.homogeneousCochains.d_eq]
  simp only [homogeneousCochainsUliftXIsoSameUniverse,
    Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, invariantsUliftIso_naturality]
  rw [Category.assoc, invariantsMap_comp,
    resolutionUliftIsoSameUniverse_d_comm, ← invariantsMap_comp,
    ← Category.assoc]

/-- In one common small universe, raising the homogeneous cochain complex is
isomorphic to taking homogeneous cochains after raising the acting group and
coefficient carrier. -/
noncomputable def homogeneousCochainsUliftIsoSameUniverse
    (X : TopRep.{v} k G) :
    ((TopModuleCat.uliftFunctor.{v, v} k).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj X.homogeneousCochains ≅
      (TopRep.ulift.{u, v, v, v, v} X).homogeneousCochains :=
  HomologicalComplex.Hom.isoOfComponents
    (homogeneousCochainsUliftXIsoSameUniverse X) (by
      rintro i j (rfl : i + 1 = j)
      exact (homogeneousCochainsUliftXIsoSameUniverse_comm X i).symm)

/-- The same-universe homogeneous-cochain comparison is natural in the
coefficient representation. -/
@[reassoc]
lemma homogeneousCochainsUliftIsoSameUniverse_naturality
    {X Y : TopRep.{v} k G} (f : X ⟶ Y) :
    ((TopModuleCat.uliftFunctor.{v, v} k).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
          (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f) ≫
        (homogeneousCochainsUliftIsoSameUniverse Y).hom =
      (homogeneousCochainsUliftIsoSameUniverse X).hom ≫
        ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id (ULift.{v} G))
          (TopRep.uliftMap.{u, v, v, v, v} f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    homogeneousCochainsUliftIsoSameUniverse,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    homogeneousCochainsUliftXIsoSameUniverse, Iso.trans_hom,
    Functor.mapIso_hom]
  ext x
  apply Subtype.ext
  exact congrArg (fun q => q.hom (ULift.up x.down.1))
    (resolutionUliftIsoSameUniverse_naturality f (n + 1))

end TopRep
