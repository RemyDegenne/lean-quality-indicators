/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FiniteEtaleAlgebras
public import SchemeProperties.GlobalSectionsBaseChange
public import SchemeProperties.NoetherianComponents
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.QuasiFinite.Basic

public section

/-!
# The finite-etale component scheme

For a quasi-compact scheme locally of finite type over a field, this file
selects the greatest finite-etale subalgebra of its global sections.  Its
spectrum is the finite-etale reflection of the scheme: every map to the
spectrum of a finite-etale algebra factors uniquely through it.  The canonical
map to the component scheme is flat and surjective.

All schemes and rings in the public reflection API live in one universe.  The
construction does not assume that the source is reduced, connected, separated,
or nonempty; in particular it also applies when its global-sections ring is the
zero ring.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 1.29 (the greatest
  finite-etale subalgebra of global sections), and the component-scheme
  definition and universal-property paragraph immediately before Proposition
  1.30 (its spectrum and the canonical factorization through it).
- `finite-etale-algebras`, `FiniteEtaleAlgebras/MaximalSubalgebra.lean`:
  `Subalgebra.exists_greatest_isFiniteEtale_of_finrank_le` provides the
  finite-etale subalgebra selection used here. The scheme-level reflection,
  universal property and surjectivity are project constructions, not results
  claimed from that dependency.
-/

open CategoryTheory Limits Opposite Topology
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {K : Type u} [Field K]

/-- The algebra of global sections of a scheme over `K`, inferred locally
from its structure morphism. -/
local instance globalSectionsAlgebraInstance
    (X : Over (Spec (.of K))) : Algebra K Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra K

/-- The affine scheme over `Spec K` associated to a `K`-algebra. -/
abbrev specOver (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- The map to an affine scheme over `K` corresponding to an algebra map into
global sections. -/
@[expose]
def toSpecOver
    (X : Over (Spec (.of K))) {A : Type u} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] Γ(X.left, ⊤)) : X ⟶ specOver K A := by
  let g : X.left ⟶ Spec (.of A) :=
    X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  refine Over.homMk g ?_
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (.of K)).inv ≫
      (g ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop =
    (Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop
  rw [cancel_epi]
  dsimp only [g]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
    Scheme.ΓSpecIso_naturality_assoc]
  ext x
  change f (algebraMap K A ((Scheme.ΓSpecIso (.of K)).hom x)) =
    X.hom.appTop x
  rw [f.commutes]
  change (((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop)
    ((Scheme.ΓSpecIso (.of K)).hom x)) = X.hom.appTop x
  simp

/-- The contravariant map of affine schemes over `K` induced by an algebra
homomorphism. -/
@[expose]
def specOverMap {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (g : B →ₐ[K] A) :
    specOver K A ⟶ specOver K B := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom g.toRingHom)) ?_
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact g.commutes x

/-- Scalar extension of a scheme over `Spec K` along `K → L`. -/
abbrev schemeBaseChange
    {K L : Type u} [CommRing K] [CommRing L] [Algebra K L]
    (X : Over (Spec (.of K))) : Over (Spec (.of L)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X

/-- The standard affine identification of the scalar extension of `Spec A`
with the spectrum of `A ⊗[K] L`. -/
@[expose]
def baseChangeSpecIso
    (K A L : Type u) [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L] :
    (schemeBaseChange ((Spec (.of A)).asOver (Spec (.of K)))
      (L := L)).left ≅ Spec (.of (A ⊗[K] L)) :=
  pullbackSpecIso K A L

/-- The standard affine scalar-extension identification in the over category. -/
@[expose]
def baseChangeSpecOverIso
    (K A L : Type u) [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L] :
    schemeBaseChange ((Spec (.of A)).asOver (Spec (.of K))) (L := L) ≅
      Over.mk (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := A)
          (B := L)).toRingHom)) :=
  Over.isoMk (pullbackSpecIso K A L) (pullbackSpecIso_hom_snd K A L)

/-- Scalar extension of a morphism over `Spec K`. -/
abbrev baseChangeMap
    {K L : Type u} [CommRing K] [CommRing L] [Algebra K L]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y) :
    schemeBaseChange X (L := L) ⟶ schemeBaseChange Y (L := L) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f

private theorem toSpecOver_appTop_injective
    (X : Over (Spec (.of K))) {A : Type u} [CommRing A] [Algebra K A]
    (f : A →ₐ[K] Γ(X.left, ⊤)) (hf : Function.Injective f) :
    Function.Injective (toSpecOver X f).left.appTop := by
  change Function.Injective
    (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)).appTop
  intro x y hxy
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality] at hxy
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of A)).hom).1
  exact hf hxy

/-- If `A` is finite over a field, an injective algebra map from `A` into
global sections induces a surjective map to `Spec A`. -/
theorem surjective_toSpecOver
    (X : Over (Spec (.of K))) [CompactSpace X.left]
    {A : Type u} [CommRing A] [Algebra K A] [Module.Finite K A]
    (f : A →ₐ[K] Γ(X.left, ⊤)) (hf : Function.Injective f) :
    Surjective (toSpecOver X f).left := by
  change Surjective
    (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom))
  let _ : DiscreteTopology (Spec (.of A)) :=
    Algebra.QuasiFinite.discreteTopology_primeSpectrum K A
  let _ : IsDominant
      (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    isDominant_of_of_appTop_injective (toSpecOver_appTop_injective X f hf)
  exact ⟨denseRange_discrete.mp
    (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)).denseRange⟩

/-- Surjectivity is preserved by scalar extension in the over category. -/
theorem surjective_baseChangeMap
    {K L : Type u} [CommRing K] [CommRing L] [Algebra K L]
    {X Y : Over (Spec (.of K))} (f : X ⟶ Y) (hf : Surjective f.left) :
    Surjective (baseChangeMap (L := L) f).left :=
  (show MorphismProperty Scheme from @Surjective).overPullbackMap _ f hf

/-- After the standard affine identification, a surjective base-changed map
still is surjective. -/
theorem surjective_baseChangeMap_comp_baseChangeSpecIso
    {K A L : Type u} [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L] {X : Over (Spec (.of K))}
    (f : X ⟶ (Spec (.of A)).asOver (Spec (.of K)))
    (hf : Surjective f.left) :
    Surjective ((baseChangeMap (L := L) f).left ≫
      (baseChangeSpecIso K A L).hom) := by
  let _ : Surjective (baseChangeMap (L := L) f).left :=
    surjective_baseChangeMap f hf
  infer_instance

/-- A finite-algebra spectrum map remains surjective after scalar extension. -/
theorem surjective_scalarExtension_toSpecOver
    {A L : Type u} [CommRing A] [CommRing L] [Algebra K A]
    [Module.Finite K A] [Algebra K L]
    (X : Over (Spec (.of K))) [CompactSpace X.left]
    (f : A →ₐ[K] Γ(X.left, ⊤)) (hf : Function.Injective f) :
    Surjective
      ((baseChangeMap (L := L) (toSpecOver X f)).left ≫
        (baseChangeSpecIso K A L).hom) := by
  apply surjective_baseChangeMap_comp_baseChangeSpecIso
  exact surjective_toSpecOver X f hf

/-- After extension to a separably closed field, the rank of a finite-etale
subalgebra of global sections is bounded by the number of connected components
of the base-changed scheme. -/
theorem finrank_le_natCard_connectedComponents_scalarExtension
    {A L : Type u} [CommRing A] [Field L] [IsSepClosed L]
    [Algebra K A] [Module.Finite K A] [Algebra.Etale K A] [Algebra K L]
    (X : Over (Spec (.of K))) [CompactSpace X.left]
    [TopologicalSpace.NoetherianSpace ((schemeBaseChange X (L := L)).left)]
    (f : A →ₐ[K] Γ(X.left, ⊤)) (hf : Function.Injective f) :
    Module.finrank K A ≤
      Nat.card (ConnectedComponents (schemeBaseChange X (L := L)).left) := by
  let _ : Algebra L (A ⊗[K] L) :=
    (Algebra.TensorProduct.includeRight (R := K) (A := A)
      (B := L)).toRingHom.toAlgebra
  let _ : Module.Finite L (A ⊗[K] L) :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight K L A).toLinearEquiv
  let _ : Algebra.Etale L (A ⊗[K] L) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight K L A)
  have hFiniteEtale : Algebra.IsFiniteEtale L (A ⊗[K] L) :=
    ⟨inferInstance, inferInstance⟩
  let _ : Finite (ConnectedComponents (schemeBaseChange X (L := L)).left) :=
    inferInstance
  let g : (schemeBaseChange X (L := L)).left ⟶ Spec (.of (A ⊗[K] L)) :=
    (baseChangeMap (L := L) (toSpecOver X f)).left ≫
      (baseChangeSpecIso K A L).hom
  calc
    Module.finrank K A = Module.finrank L (L ⊗[K] A) :=
      (Module.finrank_baseChange (R := L) (S := K) (M' := A)).symm
    _ = Module.finrank L (A ⊗[K] L) :=
      (Algebra.TensorProduct.commRight K L A).toLinearEquiv.finrank_eq
    _ ≤ Nat.card (ConnectedComponents (schemeBaseChange X (L := L)).left) :=
      hFiniteEtale.finrank_le_natCard_connectedComponents_of_surjective
        g (Scheme.Hom.continuous g)
          (surjective_scalarExtension_toSpecOver X f hf).surj

private theorem exists_greatest_isFiniteEtaleSubalgebra_globalSections_of_extension
    {L : Type u} [Field L] [IsSepClosed L] [Algebra K L]
    (X : Over (Spec (.of K))) [CompactSpace X.left]
    [TopologicalSpace.NoetherianSpace ((schemeBaseChange X (L := L)).left)] :
    ∃ A : Subalgebra K Γ(X.left, ⊤), A.IsFiniteEtale ∧
      ∀ B : Subalgebra K Γ(X.left, ⊤), B.IsFiniteEtale → B ≤ A := by
  apply Subalgebra.exists_greatest_isFiniteEtale_of_finrank_le
    (Nat.card (ConnectedComponents (schemeBaseChange X (L := L)).left))
  intro A hA
  let _ : Module.Finite K A := hA.1
  let _ : Algebra.Etale K A := hA.2
  exact finrank_le_natCard_connectedComponents_scalarExtension X A.val
    Subtype.val_injective

/-- The global sections have a greatest finite-etale `K`-subalgebra, using
`finite-etale-algebras`'s `Subalgebra.exists_greatest_isFiniteEtale_of_finrank_le`
after the scheme-specific rank bound. This is the assertion of J. S. Milne,
*Algebraic Groups* (2017), Proposition 1.29. -/
theorem exists_greatest_isFiniteEtaleSubalgebra_globalSections
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    ∃ A : Subalgebra K Γ(X.left, ⊤), A.IsFiniteEtale ∧
      ∀ B : Subalgebra K Γ(X.left, ⊤), B.IsFiniteEtale → B ≤ A := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let X_L := schemeBaseChange X (L := AlgebraicClosure K)
  let _ : CompactSpace X_L.left := by
    dsimp only [X_L, schemeBaseChange]
    exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd X.hom (Spec.map (CommRingCat.ofHom
        (algebraMap K (AlgebraicClosure K)))))
  let _ : IsNoetherian X_L.left := by
    let _ : LocallyOfFiniteType
        (pullback.snd X.hom (Spec.map (CommRingCat.ofHom
          (algebraMap K (AlgebraicClosure K))))) := inferInstance
    exact
      { toIsLocallyNoetherian :=
          LocallyOfFiniteType.isLocallyNoetherian
            (pullback.snd X.hom (Spec.map (CommRingCat.ofHom
              (algebraMap K (AlgebraicClosure K))))) }
  exact exists_greatest_isFiniteEtaleSubalgebra_globalSections_of_extension
    (L := AlgebraicClosure K) X

/-- A selected greatest finite-etale subalgebra of the global sections, as in
J. S. Milne, *Algebraic Groups* (2017), Proposition 1.29. -/
@[expose]
def componentSubalgebra
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : Subalgebra K Γ(X.left, ⊤) :=
  Classical.choose (exists_greatest_isFiniteEtaleSubalgebra_globalSections X)

/-- The selected component subalgebra is finite etale. -/
theorem componentSubalgebra_isFiniteEtale
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : (componentSubalgebra X).IsFiniteEtale :=
  (Classical.choose_spec
    (exists_greatest_isFiniteEtaleSubalgebra_globalSections X)).1

/-- Every finite-etale subalgebra of global sections lies in the selected one. -/
theorem isFiniteEtaleSubalgebra_le_componentSubalgebra
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (A : Subalgebra K Γ(X.left, ⊤))
    (hA : A.IsFiniteEtale) : A ≤ componentSubalgebra X :=
  (Classical.choose_spec
    (exists_greatest_isFiniteEtaleSubalgebra_globalSections X)).2 A hA

/-- The selected subalgebra agrees with any other greatest finite-etale
subalgebra. -/
theorem componentSubalgebra_eq_of_isGreatest
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] (A : Subalgebra K Γ(X.left, ⊤))
    (hA : A.IsFiniteEtale)
    (hgreatest : ∀ B : Subalgebra K Γ(X.left, ⊤),
      B.IsFiniteEtale → B ≤ A) :
    componentSubalgebra X = A := by
  apply le_antisymm
  · exact hgreatest _ (componentSubalgebra_isFiniteEtale X)
  · exact isFiniteEtaleSubalgebra_le_componentSubalgebra X A hA

/-- The affine finite-etale component object selected from global sections.
It is the spectrum of the component algebra in J. S. Milne, *Algebraic
Groups* (2017), in the paragraph immediately before Proposition 1.30. -/
abbrev componentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : Over (Spec (.of K)) :=
  specOver K (componentSubalgebra X)

/-- The canonical map from a scheme to its finite-etale component scheme,
as in J. S. Milne, *Algebraic Groups* (2017), in the paragraph immediately
before Proposition 1.30. -/
@[expose]
def toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : X ⟶ componentScheme X :=
  toSpecOver X (componentSubalgebra X).val

/-- The canonical map to the component scheme is surjective. -/
theorem surjective_toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : Surjective (toComponentScheme X).left := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : Module.Finite K (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).1
  exact surjective_toSpecOver X (componentSubalgebra X).val
    Subtype.val_injective

/-- The canonical map to the component scheme is flat. -/
instance flat_toComponentScheme
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : Flat (toComponentScheme X).left := by
  let : Module.Finite K (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).1
  let : Algebra.Etale K (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).2
  let : _root_.IsReduced (componentSubalgebra X) :=
    Algebra.FormallyUnramified.isReduced_of_field K _
  let : IsArtinianRing (componentSubalgebra X) := IsArtinianRing.of_finite K _
  let : IsLocallyArtinian (componentScheme X).left :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  let : DiscreteTopology (componentScheme X).left := inferInstance
  let : IsReduced (componentScheme X).left := by
    change IsReduced (Spec (.of (componentSubalgebra X)))
    infer_instance
  let Y := (componentScheme X).left
  let : DiscreteTopology Y :=
    inferInstanceAs (DiscreteTopology (componentScheme X).left)
  let : IsReduced Y := inferInstanceAs (IsReduced (componentScheme X).left)
  let Ucov : Y.OpenCover := Y.openCoverOfIsOpenCover
    (fun y : Y ↦ ⟨{y}, isOpen_discrete _⟩) (.mk (by ext; simp))
  let : IsZariskiLocalAtTarget (@Flat) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (@Flat) (Q := RingHom.Flat)
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat)
    (f := (toComponentScheme X).left) Ucov]
  intro i
  let : Subsingleton (Ucov.X i) := ⟨fun a b ↦
    Subtype.ext (Set.subsingleton_singleton a.property b.property)⟩
  let : Nonempty (Ucov.X i) := ⟨⟨i, Set.mem_singleton i⟩⟩
  let : IsReduced (Ucov.X i) := isReduced_of_isOpenImmersion (Ucov.f i)
  let : IsIntegral (Ucov.X i) :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
      ⟨⟨inferInstance⟩, inferInstance⟩
  infer_instance

/-- The algebra map on global sections induced by a map to an affine scheme
over `K`. -/
@[expose]
def algebraMapOfToSpec
    (X : Over (Spec (.of K))) {B : Type u} [CommRing B] [Algebra K B]
    (f : X ⟶ specOver K B) : B →ₐ[K] Γ(X.left, ⊤) where
  toRingHom := ((Scheme.ΓSpecIso (.of B)).inv ≫ f.left.appTop).hom
  commutes' x := by
    change (CommRingCat.ofHom (algebraMap K B) ≫
        (Scheme.ΓSpecIso (.of B)).inv ≫ f.left.appTop) x =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) x
    have hw := congrArg Scheme.Hom.appTop f.w
    change (Spec.map (CommRingCat.ofHom (algebraMap K B))).appTop ≫
      f.left.appTop = X.hom.appTop at hw
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, hw]

/-- Recovering an affine-target map from its map on global sections gives the
original map. -/
theorem toSpecOver_algebraMapOfToSpec
    (X : Over (Spec (.of K))) {B : Type u} [CommRing B] [Algebra K B]
    (f : X ⟶ specOver K B) :
    toSpecOver X (algebraMapOfToSpec X f) = f := by
  apply Over.OverMorphism.ext
  change X.left.toSpecΓ ≫ Spec.map
      ((Scheme.ΓSpecIso (.of B)).inv ≫ f.left.appTop) = f.left
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  change f.left ≫ (Spec (.of B)).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (.of B)).inv = f.left
  rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
  simp

/-- Composition with a contravariant `Spec` map corresponds to composition of
algebra maps. -/
theorem toSpecOver_comp_specOverMap
    (X : Over (Spec (.of K))) {A B : Type u}
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (f : A →ₐ[K] Γ(X.left, ⊤)) (g : B →ₐ[K] A) :
    toSpecOver X f ≫ specOverMap g = toSpecOver X (f.comp g) := by
  apply Over.OverMorphism.ext
  change (X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom g.toRingHom) =
    X.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (f.comp g).toRingHom)
  rw [Category.assoc, ← Spec.map_comp]
  congr 2

/-- The range of the algebra map induced by a finite-etale target is finite
etale. -/
theorem range_algebraMapOfToSpec_isFiniteEtale
    (X : Over (Spec (.of K))) {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    (algebraMapOfToSpec X f).range.IsFiniteEtale :=
  Algebra.IsFiniteEtale.of_surjective hB
    (algebraMapOfToSpec X f).rangeRestrict
    (AlgHom.rangeRestrict_surjective _)

/-- The range of a map from a finite-etale algebra lies in the selected
component subalgebra. -/
theorem range_algebraMapOfToSpec_le_componentSubalgebra
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    (algebraMapOfToSpec X f).range ≤ componentSubalgebra X :=
  isFiniteEtaleSubalgebra_le_componentSubalgebra X _
    (range_algebraMapOfToSpec_isFiniteEtale X hB f)

/-- The algebra map defining the universal factor. -/
@[expose]
def componentFactorAlgHom
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    B →ₐ[K] componentSubalgebra X :=
  (Subalgebra.inclusion
      (range_algebraMapOfToSpec_le_componentSubalgebra X hB f)).comp
    (algebraMapOfToSpec X f).rangeRestrict

/-- The factor from the component scheme to a finite-etale affine target. -/
@[expose]
def componentFactor
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    componentScheme X ⟶ specOver K B :=
  specOverMap (componentFactorAlgHom X hB f)

/-- The universal factor makes the canonical triangle commute. -/
theorem toComponentScheme_comp_componentFactor
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    toComponentScheme X ≫ componentFactor X hB f = f := by
  dsimp only [toComponentScheme, componentFactor, componentScheme]
  rw [toSpecOver_comp_specOverMap]
  have hcomp : (componentSubalgebra X).val.comp
      (componentFactorAlgHom X hB f) = algebraMapOfToSpec X f := by
    ext x
    rfl
  rw [hcomp, toSpecOver_algebraMapOfToSpec]

private theorem toComponentScheme_appTop_injective
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Injective (toComponentScheme X).left.appTop :=
  toSpecOver_appTop_injective X (componentSubalgebra X).val
    Subtype.val_injective

/-- Every map to a finite-etale affine scheme factors uniquely through the
component scheme. This is the universal property in J. S. Milne,
*Algebraic Groups* (2017), in the paragraph immediately before Proposition
1.30; the target may be the spectrum of any finite-etale `K`-algebra. -/
theorem componentScheme_universal
    (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {B : Type u} [CommRing B] [Algebra K B]
    (hB : Algebra.IsFiniteEtale K B) (f : X ⟶ specOver K B) :
    ∃! g : componentScheme X ⟶ specOver K B,
      toComponentScheme X ≫ g = f := by
  refine ⟨componentFactor X hB f,
    toComponentScheme_comp_componentFactor X hB f, ?_⟩
  intro g hg
  apply Over.OverMorphism.ext
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (.of B)).inv ≫ g.left.appTop =
    (Scheme.ΓSpecIso (.of B)).inv ≫
      (componentFactor X hB f).left.appTop
  ext x
  apply toComponentScheme_appTop_injective X
  change (toComponentScheme X).left.appTop
      (g.left.appTop ((Scheme.ΓSpecIso (.of B)).inv x)) =
    (toComponentScheme X).left.appTop
      ((componentFactor X hB f).left.appTop
        ((Scheme.ΓSpecIso (.of B)).inv x))
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply] using
    congrArg
      (fun q ↦ q.left.appTop ((Scheme.ΓSpecIso (.of B)).inv x))
      (hg.trans (toComponentScheme_comp_componentFactor X hB f).symm)

end

end AlgebraicGeometry
