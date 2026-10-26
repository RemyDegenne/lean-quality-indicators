/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ComponentScheme
public import SchemeProperties.GeometricConnectedness
public import FiniteEtaleAlgebras.PurelyInseparableDescent
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

public section

/-!
# Component schemes commute with field extension

For a quasi-compact scheme locally of finite type over a field, this file
constructs the canonical comparison from the component scheme after scalar
extension to the scalar extension of the component scheme, and proves that it
is an isomorphism for every extension field.

The comparison is stated first on coordinate algebras, with the tensor factors
oriented exactly as in the standard pullback of an affine scheme.  Its range is
finite etale and therefore lies in the selected component subalgebra after
base change.  The corresponding map of spectra is the canonical
comparison.  No algebraicity, finite-dimensionality, separability,
perfectness, reducedness, connectedness, nonemptiness, or separatedness
assumption is imposed.  In particular, the result applies to transcendental
and mixed extensions and to schemes with subsingleton global sections.

## References

- J. S. Milne, *Algebraic Groups* (2017), Proposition 1.30(a) and the
  following compatibility sentence: the component scheme and its canonical
  map commute with arbitrary extensions of the base field.
- `finite-etale-algebras`, `FiniteEtaleAlgebras/PurelyInseparableDescent.lean`:
  `PurelyInseparableDescent.package` and `package_range` are applied to the
  selected subalgebra in the purely inseparable comparison step.
- `finite-etale-algebras`, `FiniteEtaleAlgebras/SeparableClosureDescent.lean`:
  `SeparableClosureDescent.package` and `package_range` supply the descent
  step after separable closure. The canonical comparison for arbitrary field
  extensions is constructed here, not supplied by either upstream module.
-/

open CategoryTheory Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The structure algebra on global sections used throughout this module. -/
local instance componentGlobalSectionsAlgebra
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

/-- The algebra structure on the right-oriented tensor model. -/
local instance tensorProductRightAlgebra
    (A : Type u) [CommRing A] [Algebra k A] :
    Algebra K (A ⊗[k] K) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra

local instance baseChangeLocallyOfFiniteType
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (schemeBaseChange X (L := K)).hom := by
  change LocallyOfFiniteType
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

local instance baseChangeQuasiCompact
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (schemeBaseChange X (L := K)).hom := by
  change QuasiCompact
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

/-- Reading back the global-sections algebra map of an affinization recovers
the algebra map used to construct it. -/
private theorem algebraMapOfToSpec_toSpecOver
    {F A : Type u} [Field F] [CommRing A] [Algebra F A]
    (X : Over (Spec (.of F))) (f : A →ₐ[F] Γ(X.left, ⊤)) :
    algebraMapOfToSpec X (toSpecOver X f) = f := by
  ext x
  change ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop ≫
      X.left.toSpecΓ.appTop) x = f x
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc,
    Scheme.toSpecΓ_appTop]
  simp

/-- The canonical global-sections equivalence for the base change of an
algebraic scheme. -/
private noncomputable def componentGlobalSectionsBaseChangeEquiv
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    K ⊗[k] Γ(X.left, ⊤) ≃ₐ[K]
      Γ((schemeBaseChange X (L := K)).left, ⊤) := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact Scheme.globalSectionsBaseChangeEquiv k K X.hom

/-- The canonical scalar-extension map from the coordinate algebra of the
base-changed component scheme to the global sections of the base-changed
source scheme.

The source is `componentSubalgebra X ⊗[k] K`, matching
`baseChangeSpecOverIso`; internally the global-sections equivalence
uses the factor-reversed tensor product. -/
noncomputable def componentScalarExtensionAlgHom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra X ⊗[k] K →ₐ[K]
      Γ((schemeBaseChange X (L := K)).left, ⊤) :=
  (componentGlobalSectionsBaseChangeEquiv (K := K) X).toAlgHom.comp
    ((SeparableClosureDescent.scalarExtensionMap
      (K := K) (componentSubalgebra X)).comp
        (Algebra.TensorProduct.commRight k K (componentSubalgebra X)).symm.toAlgHom)

/-- The range of the scalar-extended selected component algebra. -/
abbrev baseChangedComponentSubalgebra
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Subalgebra K Γ((schemeBaseChange X (L := K)).left, ⊤) :=
  (componentScalarExtensionAlgHom (K := K) X).range

/-- The scalar-extended selected component algebra is finite etale over the
extension field. -/
private theorem componentAlgebraTensor_isFiniteEtale
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Algebra.IsFiniteEtale K (componentSubalgebra X ⊗[k] K) := by
  let _ : Module.Finite k (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).1
  let _ : Algebra.Etale k (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).2
  let _ : Module.Finite K (componentSubalgebra X ⊗[k] K) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight k K
        (componentSubalgebra X)).toLinearEquiv
  let _ : Algebra.Etale K (componentSubalgebra X ⊗[k] K) :=
    Algebra.Etale.of_equiv
      (Algebra.TensorProduct.commRight k K (componentSubalgebra X))
  exact ⟨inferInstance, inferInstance⟩

/-- The scalar-extended selected component algebra is finite etale over the
extension field. -/
private theorem baseChangedComponentSubalgebra_isFiniteEtale
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (baseChangedComponentSubalgebra (K := K) X).IsFiniteEtale := by
  exact Algebra.IsFiniteEtale.of_surjective
    (componentAlgebraTensor_isFiniteEtale (K := K) X)
    (componentScalarExtensionAlgHom (K := K) X).rangeRestrict
    (AlgHom.rangeRestrict_surjective _)

/-- The canonical easy inclusion: scalar extension of the selected component
algebra lies in the selected component algebra after base change. -/
private theorem baseChangedComponentSubalgebra_le
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    baseChangedComponentSubalgebra (K := K) X ≤
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  isFiniteEtaleSubalgebra_le_componentSubalgebra
    (schemeBaseChange X (L := K)) _
    (baseChangedComponentSubalgebra_isFiniteEtale (K := K) X)

/-- The selected component algebra after base change, transported back to the
tensor-product model of global sections. -/
private noncomputable def pulledBackComponentSubalgebra
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Subalgebra K (K ⊗[k] Γ(X.left, ⊤)) :=
  (componentSubalgebra (schemeBaseChange X (L := K))).map
    (componentGlobalSectionsBaseChangeEquiv (K := K) X).symm.toAlgHom

/-- Transport through the canonical global-sections equivalence preserves the
finite-etale property of the selected component algebra. -/
private theorem pulledBackComponentSubalgebra_isFiniteEtale
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (pulledBackComponentSubalgebra (K := K) X).IsFiniteEtale := by
  let e := componentGlobalSectionsBaseChangeEquiv (K := K) X
  let A := componentSubalgebra (schemeBaseChange X (L := K))
  let eA : A ≃ₐ[K] pulledBackComponentSubalgebra (K := K) X :=
    Subalgebra.equivMapOfInjective A e.symm.toAlgHom e.symm.injective
  let _ : Module.Finite K A :=
    (componentSubalgebra_isFiniteEtale (schemeBaseChange X (L := K))).1
  let _ : Algebra.Etale K A :=
    (componentSubalgebra_isFiniteEtale (schemeBaseChange X (L := K))).2
  exact ⟨Module.Finite.equiv eA.toLinearEquiv, Algebra.Etale.of_equiv eA⟩

/-- Purely inseparable base change to a separably closed field creates no new
selected finite-etale global sections.  This is the reverse inclusion
in the ambient global-sections ring, not merely an abstract equivalence. -/
private theorem componentSubalgebra_le_baseChangedComponentSubalgebra_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra (schemeBaseChange X (L := K)) ≤
      baseChangedComponentSubalgebra (K := K) X := by
  let e := componentGlobalSectionsBaseChangeEquiv (K := K) X
  let P := pulledBackComponentSubalgebra (K := K) X
  have hP : P.IsFiniteEtale :=
    pulledBackComponentSubalgebra_isFiniteEtale (K := K) X
  let pkg := PurelyInseparableDescent.package P hP
  have hD : pkg.algebra ≤ componentSubalgebra X :=
    isFiniteEtaleSubalgebra_le_componentSubalgebra X pkg.algebra
      pkg.isFiniteEtale
  let inclusion : pkg.algebra →ₐ[k] componentSubalgebra X :=
    Subalgebra.inclusion hD
  have hmap :
      (SeparableClosureDescent.scalarExtensionMap
          (K := K) (componentSubalgebra X)).comp
          (Algebra.TensorProduct.map (AlgHom.id K K) inclusion) =
        SeparableClosureDescent.scalarExtensionMap (K := K) pkg.algebra := by
    ext d
    rfl
  intro x hx
  have hxP : e.symm x ∈ P := by
    exact ⟨x, hx, rfl⟩
  have hxrange : e.symm x ∈
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) pkg.algebra).range := by
    rw [PurelyInseparableDescent.package_range P hP]
    exact hxP
  obtain ⟨z, hz⟩ := hxrange
  let w : componentSubalgebra X ⊗[k] K :=
    Algebra.TensorProduct.commRight k K (componentSubalgebra X)
      (Algebra.TensorProduct.map (AlgHom.id K K) inclusion z)
  refine ⟨w, ?_⟩
  change e
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) (componentSubalgebra X)
        ((Algebra.TensorProduct.commRight k K
          (componentSubalgebra X)).symm w)) = x
  rw [show (Algebra.TensorProduct.commRight k K
      (componentSubalgebra X)).symm w =
      Algebra.TensorProduct.map (AlgHom.id K K) inclusion z by
        simp [w]]
  change e (((SeparableClosureDescent.scalarExtensionMap
    (K := K) (componentSubalgebra X)).comp
      (Algebra.TensorProduct.map (AlgHom.id K K) inclusion)) z) = x
  rw [hmap]
  calc
    e ((SeparableClosureDescent.scalarExtensionMap
        (K := K) pkg.algebra) z) = e (e.symm x) := congrArg e hz
    _ = x := e.apply_symm_apply x

/-- In the purely inseparable/separably-closed case, the two canonical
finite-etale subalgebras are equal inside the global-sections ring. -/
private theorem baseChangedComponentSubalgebra_eq_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    baseChangedComponentSubalgebra (K := K) X =
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  le_antisymm (baseChangedComponentSubalgebra_le (K := K) X)
    (componentSubalgebra_le_baseChangedComponentSubalgebra_of_purelyInseparable
      (K := K) X)

/-- The contravariant algebra map defining the canonical comparison of
component schemes. -/
noncomputable def componentBaseChangeComparisonAlgHom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra X ⊗[k] K →ₐ[K]
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  (componentScalarExtensionAlgHom (K := K) X).codRestrict
    (componentSubalgebra (schemeBaseChange X (L := K)))
    fun z ↦ baseChangedComponentSubalgebra_le (K := K) X
      ⟨z, rfl⟩

/-- The scalar-extension map is injective.  This includes the zero or
subsingleton ambient global-sections ring: no nontriviality hypothesis is
used. -/
private theorem componentScalarExtensionAlgHom_injective
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Injective (componentScalarExtensionAlgHom (K := K) X) := by
  let e := componentGlobalSectionsBaseChangeEquiv (K := K) X
  let swap :=
    (Algebra.TensorProduct.commRight k K (componentSubalgebra X)).symm
  have hscalar : Function.Injective
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) (componentSubalgebra X)) := by
    change Function.Injective
      ((componentSubalgebra X).val.toLinearMap.baseChange K)
    exact Module.Flat.lTensor_preserves_injective_linearMap
      (componentSubalgebra X).val.toLinearMap Subtype.val_injective
  intro x y hxy
  change e
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) (componentSubalgebra X) (swap x)) =
    e
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) (componentSubalgebra X) (swap y)) at hxy
  exact swap.injective (hscalar (e.injective hxy))

/-- The contravariant algebra comparison is always injective. -/
theorem componentBaseChangeComparisonAlgHom_injective
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Injective (componentBaseChangeComparisonAlgHom (K := K) X) := by
  intro x y hxy
  apply componentScalarExtensionAlgHom_injective (K := K) X
  exact congrArg Subtype.val hxy

/-- In the purely inseparable/separably-closed case, the canonical algebra
comparison is surjective as well as injective. -/
private theorem componentBaseChangeComparisonAlgHom_surjective_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (componentBaseChangeComparisonAlgHom (K := K) X) := by
  intro y
  have hy : (y : Γ((schemeBaseChange X (L := K)).left, ⊤)) ∈
      baseChangedComponentSubalgebra (K := K) X := by
    rw [baseChangedComponentSubalgebra_eq_of_purelyInseparable (K := K) X]
    exact y.property
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, Subtype.ext ?_⟩
  exact hx

/-- The canonical algebra equivalence in the purely
inseparable/separably-closed case.  Its forward map is definitionally the
canonical comparison map. -/
private noncomputable def componentBaseChangeComparisonAlgEquiv_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra X ⊗[k] K ≃ₐ[K]
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  AlgEquiv.ofBijective (componentBaseChangeComparisonAlgHom (K := K) X)
    ⟨componentBaseChangeComparisonAlgHom_injective (K := K) X,
      componentBaseChangeComparisonAlgHom_surjective_of_purelyInseparable
        (K := K) X⟩

/-- Contravariant `Spec` turns an algebra equivalence into an isomorphism of
the explicit affine schemes over the base field. -/
private def specOverIsoOfAlgEquiv
    {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (e : A ≃ₐ[K] B) :
    specOver K B ≅ specOver K A :=
  Over.isoMk
    (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) (by
      change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact e.commutes x)

/-- The forward map of `specOverIsoOfAlgEquiv` is the explicit contravariant
map induced by the forward algebra homomorphism. -/
@[simp] private theorem specOverIsoOfAlgEquiv_hom
    {A B : Type u} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (e : A ≃ₐ[K] B) :
    (specOverIsoOfAlgEquiv e).hom = specOverMap e.toAlgHom := rfl

/-- The standard affine model for the base change of `componentScheme X`. -/
private abbrev componentSchemeBaseChangeModel
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : Over (Spec (.of K)) :=
  specOver K (componentSubalgebra X ⊗[k] K)

/-- The standard pullback of `componentScheme X` is canonically isomorphic to
the explicit tensor-product affine model. -/
private def componentSchemeBaseChangeModelIso
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    schemeBaseChange (componentScheme X) (L := K) ≅
      componentSchemeBaseChangeModel (K := K) X :=
  baseChangeSpecOverIso k (componentSubalgebra X) K

/-- Base change of the canonical source map, with its target transported to
the explicit affine tensor-product model. -/
private noncomputable def baseChangedToComponentSchemeModel
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    schemeBaseChange X (L := K) ⟶
      componentSchemeBaseChangeModel (K := K) X :=
  baseChangeMap (L := K) (toComponentScheme X) ≫
    (componentSchemeBaseChangeModelIso (K := K) X).hom

/-- The transported base-changed canonical map has the expected projection to
the original component scheme. -/
private theorem baseChangedToComponentSchemeModel_fst
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (baseChangedToComponentSchemeModel (K := K) X).left ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := k) (A := componentSubalgebra X) (B := K))) =
      pullback.fst X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        (toComponentScheme X).left := by
  change (baseChangeMap (L := K) (toComponentScheme X)).left ≫
      (pullbackSpecIso k (componentSubalgebra X) K).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := k) (A := componentSubalgebra X) (B := K))) = _
  rw [pullbackSpecIso_hom_fst]
  exact pullback.lift_fst _ _ _

/-- The transported base-changed canonical map has the expected projection to
the extension-field spectrum. -/
private theorem baseChangedToComponentSchemeModel_snd
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (baseChangedToComponentSchemeModel (K := K) X).left ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := k) (A := componentSubalgebra X) (B := K) :
              K →+* componentSubalgebra X ⊗[k] K)) =
      pullback.snd X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  change (baseChangeMap (L := K) (toComponentScheme X)).left ≫
      (pullbackSpecIso k (componentSubalgebra X) K).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := k) (A := componentSubalgebra X) (B := K) :
              K →+* componentSubalgebra X ⊗[k] K)) = _
  rw [pullbackSpecIso_hom_snd]
  exact pullback.lift_snd _ _ _

/-- The map obtained directly by applying `Spec` to the canonical algebra
comparison. -/
private noncomputable def componentBaseChangeComparisonModelFromAlgHom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ⟶
      componentSchemeBaseChangeModel (K := K) X :=
  specOverMap (componentBaseChangeComparisonAlgHom (K := K) X)

/-- The canonical comparison, with its target written as the explicit affine
model of the base-changed component scheme.  It is the unique factor of the
base-changed canonical source map through the finite-etale
reflection. -/
private noncomputable def componentBaseChangeComparisonModel
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ⟶
      componentSchemeBaseChangeModel (K := K) X :=
  componentFactor (schemeBaseChange X (L := K))
    (componentAlgebraTensor_isFiniteEtale (K := K) X)
    (baseChangedToComponentSchemeModel (K := K) X)

/-- Compatibility of the model comparison with the two canonical maps from
the base-changed source scheme. -/
private theorem toComponentScheme_comp_componentBaseChangeComparisonModel
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    toComponentScheme (schemeBaseChange X (L := K)) ≫
        componentBaseChangeComparisonModel (K := K) X =
      baseChangedToComponentSchemeModel (K := K) X :=
  toComponentScheme_comp_componentFactor
    (schemeBaseChange X (L := K))
    (componentAlgebraTensor_isFiniteEtale (K := K) X)
    (baseChangedToComponentSchemeModel (K := K) X)

/-- The universal-property factor uses the canonical scalar-extension algebra
map packaged above. -/
private theorem componentFactorAlgHom_baseChangedToComponentSchemeModel
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentFactorAlgHom (schemeBaseChange X (L := K))
        (componentAlgebraTensor_isFiniteEtale (K := K) X)
        (baseChangedToComponentSchemeModel (K := K) X) =
      componentBaseChangeComparisonAlgHom (K := K) X := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  ext z
  change algebraMapOfToSpec (schemeBaseChange X (L := K))
      (baseChangedToComponentSchemeModel (K := K) X) z =
    componentScalarExtensionAlgHom (K := K) X z
  induction z using TensorProduct.inductionOn with
  | tmul p a =>
      let f := baseChangedToComponentSchemeModel (K := K) X
      have hp : algebraMapOfToSpec (schemeBaseChange X (L := K)) f
          (p ⊗ₜ[k] (1 : K)) =
          (pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop (p :
              Γ(X.left, ⊤)) := by
        change (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom
              (R := k) (A := componentSubalgebra X) (B := K)) ≫
              (Scheme.ΓSpecIso
                (.of (componentSubalgebra X ⊗[k] K))).inv ≫
              f.left.appTop) p = _
        rw [Scheme.ΓSpecIso_inv_naturality_assoc,
          ← Scheme.Hom.comp_appTop,
          baseChangedToComponentSchemeModel_fst,
          Scheme.Hom.comp_appTop]
        apply congrArg
          (pullback.fst X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
        exact congrArg (fun g ↦ g p)
          (algebraMapOfToSpec_toSpecOver X (componentSubalgebra X).val)
      have ha : algebraMapOfToSpec (schemeBaseChange X (L := K)) f
          ((1 : componentSubalgebra X) ⊗ₜ[k] a) =
          (pullback.snd X.hom
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop
              ((Scheme.ΓSpecIso (.of K)).inv a) := by
        change (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight
              (R := k) (A := componentSubalgebra X) (B := K) :
                K →+* componentSubalgebra X ⊗[k] K) ≫
              (Scheme.ΓSpecIso
                (.of (componentSubalgebra X ⊗[k] K))).inv ≫
              f.left.appTop) a = _
        rw [Scheme.ΓSpecIso_inv_naturality_assoc,
          ← Scheme.Hom.comp_appTop,
          baseChangedToComponentSchemeModel_snd]
        rfl
      rw [show p ⊗ₜ[k] a =
          (p ⊗ₜ[k] (1 : K)) *
            ((1 : componentSubalgebra X) ⊗ₜ[k] a) by simp]
      simp only [map_mul]
      rw [hp, ha]
      simp [componentScalarExtensionAlgHom,
        componentGlobalSectionsBaseChangeEquiv]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The universal-property construction of the model comparison is exactly
the map obtained by applying `Spec` to the canonical scalar-extension algebra
map. -/
private theorem componentBaseChangeComparisonModel_eq_fromAlgHom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentBaseChangeComparisonModel (K := K) X =
      componentBaseChangeComparisonModelFromAlgHom (K := K) X := by
  unfold componentBaseChangeComparisonModel
    componentBaseChangeComparisonModelFromAlgHom componentFactor
  rw [componentFactorAlgHom_baseChangedToComponentSchemeModel (K := K) X]

/-- In the purely inseparable/separably-closed case, the model comparison is
an isomorphism induced by the canonical algebra equivalence. -/
private noncomputable def componentBaseChangeComparisonModelIso_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ≅
      componentSchemeBaseChangeModel (K := K) X :=
  specOverIsoOfAlgEquiv
    (componentBaseChangeComparisonAlgEquiv_of_purelyInseparable (K := K) X)

/-- The forward map of the purely inseparable model isomorphism is the
canonical comparison constructed from the universal property. -/
private theorem componentBaseChangeComparisonModelIso_hom_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (componentBaseChangeComparisonModelIso_of_purelyInseparable
      (K := K) X).hom = componentBaseChangeComparisonModel (K := K) X := by
  rw [componentBaseChangeComparisonModel_eq_fromAlgHom (K := K) X]
  rfl

/-- The canonical comparison from the selected component scheme of the
base-changed source to the categorical base change of the selected component
scheme. This is the canonical comparison of J. S. Milne, *Algebraic Groups*
(2017), Proposition 1.30(a), for an arbitrary field extension. -/
noncomputable def componentBaseChangeComparison
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ⟶
      schemeBaseChange (componentScheme X) (L := K) :=
  componentBaseChangeComparisonModel (K := K) X ≫
    (componentSchemeBaseChangeModelIso (K := K) X).inv

/-- The canonical categorical base-change isomorphism in the purely
inseparable/separably-closed case. -/
private noncomputable def componentBaseChangeIso_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ≅
      schemeBaseChange (componentScheme X) (L := K) :=
  (componentBaseChangeComparisonModelIso_of_purelyInseparable
    (K := K) X).trans (componentSchemeBaseChangeModelIso (K := K) X).symm

/-- The forward map of the purely inseparable categorical isomorphism is the
canonical comparison. -/
private theorem componentBaseChangeIso_hom_of_purelyInseparable
    [IsPurelyInseparable k K] [IsSepClosed K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (componentBaseChangeIso_of_purelyInseparable (K := K) X).hom =
      componentBaseChangeComparison (K := K) X := by
  rw [componentBaseChangeIso_of_purelyInseparable, Iso.trans_hom,
    componentBaseChangeComparisonModelIso_hom_of_purelyInseparable]
  rfl

/-- The canonical comparison commutes with the base-changed canonical map,
as in the sentence following J. S. Milne, *Algebraic Groups* (2017),
Proposition 1.30(a). -/
theorem toComponentScheme_comp_componentBaseChangeComparison
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    toComponentScheme (schemeBaseChange X (L := K)) ≫
        componentBaseChangeComparison (K := K) X =
      baseChangeMap (L := K) (toComponentScheme X) := by
  rw [componentBaseChangeComparison, ← Category.assoc,
    toComponentScheme_comp_componentBaseChangeComparisonModel]
  dsimp only [baseChangedToComponentSchemeModel]
  simp

end

end AlgebraicGeometry
namespace AlgebraicGeometry

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The base-field algebra structure on global sections used in this module. -/
local instance componentGlobalSectionsAlgebra'
    {F : Type u} [Field F] (X : Over (Spec (.of F))) :
    Algebra F Γ(X.left, ⊤) :=
  X.hom.globalSectionsAlgebra F

/-- The extension-field algebra structure on a right-oriented tensor product. -/
local instance tensorProductRightAlgebra'
    {F L A : Type u} [CommRing F] [CommRing L] [Algebra F L]
    [CommRing A] [Algebra F A] :
    Algebra L (A ⊗[F] L) :=
  Algebra.TensorProduct.includeRight.toRingHom.toAlgebra

local instance baseChangeLocallyOfFiniteType'
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType (schemeBaseChange X (L := K)).hom := by
  change LocallyOfFiniteType
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

local instance baseChangeQuasiCompact'
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] :
    QuasiCompact (schemeBaseChange X (L := K)).hom := by
  change QuasiCompact
    (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  infer_instance

/-! ## The split finite-etale quotient carried by connected components -/

/-- A qc locally-finite-type scheme maps canonically to one copy of the base
point for each of its connected components. -/
@[expose]
noncomputable def toConnectedComponentsSpec
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    X ⟶ specOver k (ConnectedComponents X.left → k) := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let f : X.left ⟶ Spec (.of (ConnectedComponents X.left → k)) :=
    X.left.toConnectedComponentCoproduct X.hom ≫
      sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of k)
  refine Over.homMk f ?_
  change f ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (ConnectedComponents X.left → k))) = X.hom
  rw [← cancel_epi X.left.connectedComponentSigmaIso.hom]
  apply Sigma.hom_ext
  intro c
  dsimp only [f]
  simp only [X.left.connectedComponentSigmaIso_hom_ι_assoc]
  change (X.left.connectedComponentOpen c).ι ≫
      X.left.toConnectedComponentCoproduct X.hom ≫
        (sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of k) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap k (ConnectedComponents X.left → k)))) = _
  rw [Scheme.connectedComponentOpen_ι_toConnectedComponentCoproduct_assoc]
  rw [ι_sigmaSpec_assoc, ← Spec.map_comp]
  rw [show CommRingCat.ofHom
        (algebraMap k (ConnectedComponents X.left → k)) ≫
      CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : ConnectedComponents X.left ↦ k) c) =
      𝟙 (CommRingCat.of k) by ext x; rfl]
  simp

/-- The map to the split finite-etale scheme of connected components is
surjective on the underlying spaces. -/
theorem toConnectedComponentsSpec_surjective
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (toConnectedComponentsSpec X).left := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let S := fun _ : ConnectedComponents X.left ↦ Spec (.of k)
  let e : (∐ S) ≅ Spec (.of (ConnectedComponents X.left → k)) :=
    asIso (sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of k))
  intro y
  let z : (∐ S : Scheme) := e.inv y
  obtain ⟨⟨c, p⟩, hcp⟩ := (sigmaMk S).surjective z
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  let xc : X.left.connectedComponentOpen c := ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change (sigmaSpec (fun _ : ConnectedComponents X.left ↦ .of k))
      (X.left.toConnectedComponentCoproduct X.hom x) = y
  have hcomponent : X.left.toConnectedComponentCoproduct X.hom x =
      Sigma.ι S c (X.hom x) := by
    have h := congrArg
      (fun q : (X.left.connectedComponentOpen c).toScheme ⟶ ∐ S ↦ q xc)
      (X.left.connectedComponentOpen_ι_toConnectedComponentCoproduct X.hom c)
    change X.left.toConnectedComponentCoproduct X.hom x =
      Sigma.ι S c (X.hom x) at h
    exact h
  rw [hcomponent]
  have hp : X.hom x = p := Subsingleton.elim _ _
  rw [hp, ← sigmaMk_mk, hcp]
  change e.hom (e.inv y) = y
  have h := congrArg
    (fun q : Spec (.of (ConnectedComponents X.left → k)) ⟶
        Spec (.of (ConnectedComponents X.left → k)) ↦ q.base y)
    e.inv_hom_id
  exact h

/-- The split algebra of connected components embeds into global sections via
the canonical component-decomposition map. -/
private theorem algebraMapOfToConnectedComponentsSpec_injective
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Injective (algebraMapOfToSpec X (toConnectedComponentsSpec X)) := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let C := ConnectedComponents X.left → k
  let _ : _root_.IsReduced C := by
    change _root_.IsReduced (ConnectedComponents X.left → k)
    infer_instance
  let f := (toConnectedComponentsSpec X).left
  let _ : IsReduced (specOver k (ConnectedComponents X.left → k)).left := by
    change IsReduced (Spec (.of (ConnectedComponents X.left → k)))
    infer_instance
  let _ : QuasiSeparatedSpace
      (specOver k (ConnectedComponents X.left → k)).left := by
    change QuasiSeparatedSpace (Spec (.of (ConnectedComponents X.left → k)))
    infer_instance
  let _ : Surjective f :=
    ⟨toConnectedComponentsSpec_surjective X⟩
  let _ : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hf : Function.Injective f.appTop := Scheme.Hom.app_injective f ⊤
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of C)).inv).injective
  apply hf
  exact hab

/-- Over a separably closed field, the selected component algebra has exactly
one basis vector for each connected component. -/
theorem componentSubalgebra_finrank_eq_natCard_connectedComponents
    [IsSepClosed k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Module.finrank k (componentSubalgebra X) =
      Nat.card (ConnectedComponents X.left) := by
  let _ : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace X.hom
  let _ : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  let _ : IsNoetherian X.left := ⟨⟩
  let I := ConnectedComponents X.left
  let _ : Fintype I := Fintype.ofFinite I
  have hPi : Algebra.IsFiniteEtale k (I → k) := ⟨inferInstance, inferInstance⟩
  let _ : Module.Finite k (componentSubalgebra X) :=
    (componentSubalgebra_isFiniteEtale X).1
  let f := toConnectedComponentsSpec X
  let g := componentFactorAlgHom X hPi f
  have hg : Function.Injective g := by
    intro a b hab
    apply algebraMapOfToConnectedComponentsSpec_injective X
    change algebraMapOfToSpec X f a = algebraMapOfToSpec X f b
    exact congrArg Subtype.val hab
  apply le_antisymm
  · exact Algebra.IsFiniteEtale.finrank_le_natCard_connectedComponents_of_surjective
      (componentSubalgebra_isFiniteEtale X) (toComponentScheme X).left
      (Scheme.Hom.continuous _) (surjective_toComponentScheme X).surj
  · have h := g.toLinearMap.finrank_le_finrank_of_injective hg
    simpa [I, Module.finrank_pi_fintype] using h

/-! ## Connected components in scalar-extension towers -/

/-- Base change from a separably closed field preserves the connected-component
set, including for arbitrary transcendental extensions. -/
theorem natCard_connectedComponents_schemeBaseChange_eq_of_isSepClosed
    [IsSepClosed k] (X : Over (Spec (.of k))) :
    Nat.card (ConnectedComponents (schemeBaseChange X (L := K)).left) =
      Nat.card (ConnectedComponents X.left) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let q := pullback.fst X.hom g
  let _ : GeometricallyConnected g :=
    geometricallyConnected_SpecMap_of_isSepClosed k K
  let _ : UniversallyOpen g := inferInstance
  let e := q.connectedComponentsHomeomorph q.isOpenMap
  exact Nat.card_congr e.toEquiv

/-- An isomorphism of schemes induces an equivalence of their connected
components. -/
private noncomputable def connectedComponentsEquivOfSchemeIso
    {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    ConnectedComponents Y ≃ ConnectedComponents Z where
  toFun := (Scheme.homeoOfIso e).continuous.connectedComponentsMap
  invFun := (Scheme.homeoOfIso e).symm.continuous.connectedComponentsMap
  left_inv c := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    simp
  right_inv c := by
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    simp

/-- Successive base change through a field tower has the same number of
connected components as direct base change.  If the original base is
separably closed, that is the original component count. -/
private theorem natCard_connectedComponents_iteratedBaseChange_eq_of_isSepClosed
    [IsSepClosed k] {L : Type u} [Field L] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] (X : Over (Spec (.of k))) :
    Nat.card (ConnectedComponents
        (schemeBaseChange (schemeBaseChange X (L := K)) (L := L)).left) =
      Nat.card (ConnectedComponents X.left) := by
  let e := Scheme.baseChangeTowerIso k K L X.hom
  calc
    Nat.card (ConnectedComponents
        (schemeBaseChange (schemeBaseChange X (L := K)) (L := L)).left) =
        Nat.card (ConnectedComponents (schemeBaseChange X (L := L)).left) :=
      Nat.card_congr (connectedComponentsEquivOfSchemeIso e)
    _ = Nat.card (ConnectedComponents X.left) :=
      natCard_connectedComponents_schemeBaseChange_eq_of_isSepClosed
        (K := L) X

/-- Over a separably closed base, no scalar extension can increase the rank
of the selected component algebra beyond the original component count. -/
private theorem componentSubalgebra_baseChange_finrank_le_of_isSepClosed
    [IsSepClosed k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Module.finrank K
        (componentSubalgebra (schemeBaseChange X (L := K))) ≤
      Nat.card (ConnectedComponents X.left) := by
  let L := AlgebraicClosure K
  let XK := schemeBaseChange X (L := K)
  let _ : CompactSpace XK.left :=
    QuasiCompact.compactSpace_of_compactSpace XK.hom
  let _ : IsLocallyNoetherian XK.left :=
    LocallyOfFiniteType.isLocallyNoetherian XK.hom
  let _ : Module.Finite K (componentSubalgebra XK) :=
    (componentSubalgebra_isFiniteEtale XK).1
  let _ : Algebra.Etale K (componentSubalgebra XK) :=
    (componentSubalgebra_isFiniteEtale XK).2
  let XL := schemeBaseChange XK (L := L)
  let _ : CompactSpace XL.left :=
    QuasiCompact.compactSpace_of_compactSpace XL.hom
  let _ : IsLocallyNoetherian XL.left :=
    LocallyOfFiniteType.isLocallyNoetherian XL.hom
  let _ : IsNoetherian XL.left := ⟨⟩
  have h := finrank_le_natCard_connectedComponents_scalarExtension
    (K := K) (L := L) XK
      (componentSubalgebra XK).val Subtype.val_injective
  exact h.trans_eq
    (natCard_connectedComponents_iteratedBaseChange_eq_of_isSepClosed
      (k := k) (K := K) (L := L) X)

/-! ## Separable-closure descent of the selected subalgebra -/

/-- Transporting the selected component subalgebra back through the canonical
global-sections equivalence still gives the greatest finite-etale subalgebra
of the tensor-product model. -/
private theorem isFiniteEtaleSubalgebra_le_pulledBackComponentSubalgebra
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    (Q : Subalgebra K (K ⊗[k] Γ(X.left, ⊤))) (hQ : Q.IsFiniteEtale) :
    Q ≤ pulledBackComponentSubalgebra (K := K) X := by
  let e := componentGlobalSectionsBaseChangeEquiv (K := K) X
  let eQ : Q ≃ₐ[K] Q.map e.toAlgHom :=
    Subalgebra.equivMapOfInjective Q e.toAlgHom e.injective
  have hQmap : (Q.map e.toAlgHom).IsFiniteEtale := by
    let _ : Module.Finite K Q := hQ.1
    let _ : Algebra.Etale K Q := hQ.2
    exact ⟨Module.Finite.equiv eQ.toLinearEquiv,
      Algebra.Etale.of_equiv eQ⟩
  have hle : Q.map e.toAlgHom ≤
      componentSubalgebra (schemeBaseChange X (L := K)) :=
    isFiniteEtaleSubalgebra_le_componentSubalgebra
      (schemeBaseChange X (L := K)) _ hQmap
  intro x hx
  change x ∈ (componentSubalgebra
    (schemeBaseChange X (L := K))).map e.symm.toAlgHom
  refine ⟨e x, hle ⟨x, hx, rfl⟩, ?_⟩
  exact e.symm_apply_apply x

/-- Every ambient idempotent belongs to the transported selected component
subalgebra. -/
private theorem idempotent_mem_pulledBackComponentSubalgebra
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] {e : K ⊗[k] Γ(X.left, ⊤)}
    (he : IsIdempotentElem e) :
    e ∈ pulledBackComponentSubalgebra (K := K) X := by
  obtain ⟨Q, hQ, heQ⟩ :=
    Subalgebra.exists_isFiniteEtale_of_isIdempotentElem
      (K := K) (R := K ⊗[k] Γ(X.left, ⊤)) e he
  exact isFiniteEtaleSubalgebra_le_pulledBackComponentSubalgebra
    (K := K) X Q hQ heQ

/-- The transported selected subalgebra over a separable closure is stable
under the coefficientwise absolute-Galois action. -/
private theorem pulledBackComponentSubalgebra_isStable_of_isSepClosure
    [IsSepClosure k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    GaloisDescent.IsStable
      (pulledBackComponentSubalgebra (K := K) X) := by
  classical
  let A := K ⊗[k] Γ(X.left, ⊤)
  let P := pulledBackComponentSubalgebra (K := K) X
  let _ : Module.Finite K P :=
    (pulledBackComponentSubalgebra_isFiniteEtale (K := K) X).1
  let _ : Algebra.Etale K P :=
    (pulledBackComponentSubalgebra_isFiniteEtale (K := K) X).2
  let _ : IsSepClosed K := IsSepClosure.sep_closed k
  let _ : IsArtinianRing P := isArtinian_of_tower K inferInstance
  let _ : Fintype (PrimeSpectrum P) := Fintype.ofFinite _
  let split : P ≃ₐ[K] PrimeSpectrum P → K :=
    Algebra.FormallyEtale.equivPiOfIsSepClosed K P
  let idem (i : PrimeSpectrum P) : P := split.symm (Pi.single i 1)
  have hidem : CompleteOrthogonalIdempotents idem := by
    change CompleteOrthogonalIdempotents
      (split.symm ∘ fun i : PrimeSpectrum P ↦ Pi.single i 1)
    exact (CompleteOrthogonalIdempotents.single
      (fun _ : PrimeSpectrum P ↦ K)).map split.symm.toRingHom
  intro σ x hx
  let p : P := ⟨x, hx⟩
  have hp : p = ∑ i, (split p i) • idem i := by
    apply split.injective
    ext j
    simpa [idem] using congrFun (pi_eq_sum_univ' (split p)) j
  have hxsum : x = ∑ i, (split p i) • (idem i : A) := by
    calc
      x = (p : A) := rfl
      _ = ((∑ i, (split p i) • idem i : P) : A) :=
        congrArg (fun q : P ↦ (q : A)) hp
      _ = ∑ i, (split p i) • (idem i : A) := by
        change P.val (∑ i, (split p i) • idem i) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        congr 1
  rw [hxsum, map_sum]
  apply Subalgebra.sum_mem
  intro i _
  have hsemilinear (a : K) (y : A) :
      GaloisDescent.coefficientwise (R := Γ(X.left, ⊤)) σ (a • y) =
        σ a • GaloisDescent.coefficientwise (R := Γ(X.left, ⊤)) σ y := by
    rw [Algebra.smul_def, Algebra.smul_def]
    rw [map_mul]
    congr 1
  rw [hsemilinear]
  apply P.smul_mem
  apply idempotent_mem_pulledBackComponentSubalgebra
    (K := K) X
  exact (hidem.idem i).map
    ((GaloisDescent.coefficientwise (R := Γ(X.left, ⊤)) σ).toRingHom.comp
      P.val.toRingHom)

/-- Separable-closure descent gives the reverse inclusion between the
two embedded component subalgebras. -/
private theorem componentSubalgebra_le_baseChangedComponentSubalgebra_of_isSepClosure
    [IsSepClosure k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra (schemeBaseChange X (L := K)) ≤
      baseChangedComponentSubalgebra (K := K) X := by
  let _ : Algebra K (componentSubalgebra X ⊗[k] K) :=
    Algebra.TensorProduct.rightAlgebra
  let e := componentGlobalSectionsBaseChangeEquiv (K := K) X
  let P := pulledBackComponentSubalgebra (K := K) X
  have hP : P.IsFiniteEtale :=
    pulledBackComponentSubalgebra_isFiniteEtale (K := K) X
  have hstable : GaloisDescent.IsStable P :=
    pulledBackComponentSubalgebra_isStable_of_isSepClosure (K := K) X
  let pkg := SeparableClosureDescent.package P hstable hP
  have hD : pkg.algebra ≤ componentSubalgebra X :=
    isFiniteEtaleSubalgebra_le_componentSubalgebra X pkg.algebra
      pkg.isFiniteEtale
  let inclusion : pkg.algebra →ₐ[k] componentSubalgebra X :=
    Subalgebra.inclusion hD
  have hmap :
      (SeparableClosureDescent.scalarExtensionMap
          (K := K) (componentSubalgebra X)).comp
          (Algebra.TensorProduct.map (AlgHom.id K K) inclusion) =
        SeparableClosureDescent.scalarExtensionMap (K := K) pkg.algebra := by
    ext d
    rfl
  intro x hx
  have hxP : e.symm x ∈ P := by
    exact ⟨x, hx, rfl⟩
  have hxrange : e.symm x ∈
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) pkg.algebra).range := by
    rw [SeparableClosureDescent.package_range P hstable hP]
    exact hxP
  obtain ⟨z, hz⟩ := hxrange
  let w : componentSubalgebra X ⊗[k] K :=
    Algebra.TensorProduct.commRight k K (componentSubalgebra X)
      (Algebra.TensorProduct.map (AlgHom.id K K) inclusion z)
  refine ⟨w, ?_⟩
  change e
      (SeparableClosureDescent.scalarExtensionMap
        (K := K) (componentSubalgebra X)
        ((Algebra.TensorProduct.commRight k K
          (componentSubalgebra X)).symm w)) = x
  rw [show (Algebra.TensorProduct.commRight k K
      (componentSubalgebra X)).symm w =
      Algebra.TensorProduct.map (AlgHom.id K K) inclusion z by
        simp [w]]
  change e (((SeparableClosureDescent.scalarExtensionMap
    (K := K) (componentSubalgebra X)).comp
      (Algebra.TensorProduct.map (AlgHom.id K K) inclusion)) z) = x
  rw [hmap]
  calc
    e ((SeparableClosureDescent.scalarExtensionMap
        (K := K) pkg.algebra) z) = e (e.symm x) := congrArg e hz
    _ = x := e.apply_symm_apply x

/-- The canonical component-algebra comparison is surjective after extending
to a separable closure. -/
private theorem componentBaseChangeComparisonAlgHom_surjective_of_isSepClosure
    [IsSepClosure k K]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (componentBaseChangeComparisonAlgHom (K := K) X) := by
  intro y
  have hy : (y : Γ((schemeBaseChange X (L := K)).left, ⊤)) ∈
      baseChangedComponentSubalgebra (K := K) X :=
    componentSubalgebra_le_baseChangedComponentSubalgebra_of_isSepClosure
      (K := K) X y.property
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, Subtype.ext ?_⟩
  exact hx

/-- The rank of the selected component algebra over an arbitrary field is the
number of connected components after passage to its separable closure. -/
theorem componentSubalgebra_finrank_eq_natCard_separableClosure
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Module.finrank k (componentSubalgebra X) =
      Nat.card (ConnectedComponents
        (schemeBaseChange X (L := SeparableClosure k)).left) := by
  let XS := schemeBaseChange X (L := SeparableClosure k)
  let P := componentSubalgebra X
  let Q := componentSubalgebra XS
  let f := componentBaseChangeComparisonAlgHom (K := SeparableClosure k) X
  let _ : Module.Finite k P := (componentSubalgebra_isFiniteEtale X).1
  let _ : Module.Finite (SeparableClosure k) Q :=
    (componentSubalgebra_isFiniteEtale XS).1
  let swap := Algebra.TensorProduct.commRight k (SeparableClosure k) P
  let g : SeparableClosure k ⊗[k] P →ₐ[SeparableClosure k] Q :=
    f.comp swap.toAlgHom
  have hg : Function.Bijective g := by
    constructor
    · exact (componentBaseChangeComparisonAlgHom_injective
        (K := SeparableClosure k) X).comp swap.injective
    · exact (componentBaseChangeComparisonAlgHom_surjective_of_isSepClosure
        (K := SeparableClosure k) X).comp swap.surjective
  let e : SeparableClosure k ⊗[k] P ≃ₐ[SeparableClosure k] Q :=
    AlgEquiv.ofBijective g hg
  calc
    Module.finrank k P = Module.finrank (SeparableClosure k)
        (SeparableClosure k ⊗[k] P) := Module.finrank_baseChange.symm
    _ = Module.finrank (SeparableClosure k) Q := e.toLinearEquiv.finrank_eq
    _ = Nat.card (ConnectedComponents XS.left) :=
      componentSubalgebra_finrank_eq_natCard_connectedComponents XS

/-- Geometric connected-component counts are unchanged by an arbitrary field
extension.  Both separable closures are compared inside an algebraic closure
of the larger field. -/
theorem natCard_connectedComponents_separableClosures_eq
    (X : Over (Spec (.of k))) :
    Nat.card (ConnectedComponents
        (schemeBaseChange X (L := SeparableClosure k)).left) =
      Nat.card (ConnectedComponents
        (schemeBaseChange (schemeBaseChange X (L := K))
          (L := SeparableClosure K)).left) := by
  let ks := SeparableClosure k
  let Ks := SeparableClosure K
  let L := AlgebraicClosure K
  let g : ks →ₐ[k] L := IsSepClosed.lift
  let _ : Algebra ks L := g.toAlgebra
  let _ : IsScalarTower k ks L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (g.commutes a).symm)
  let Xks := schemeBaseChange X (L := ks)
  let XK := schemeBaseChange X (L := K)
  let XKKs := schemeBaseChange XK (L := Ks)
  let XksL := schemeBaseChange Xks (L := L)
  let XKL := schemeBaseChange XK (L := L)
  let XKKsL := schemeBaseChange XKKs (L := L)
  let XL := schemeBaseChange X (L := L)
  let eks := Scheme.baseChangeTowerIso k ks L X.hom
  let eK := Scheme.baseChangeTowerIso k K L X.hom
  let eKs := Scheme.baseChangeTowerIso K Ks L XK.hom
  calc
    Nat.card (ConnectedComponents Xks.left) =
        Nat.card (ConnectedComponents XksL.left) :=
      (natCard_connectedComponents_schemeBaseChange_eq_of_isSepClosed
        (k := ks) (K := L) Xks).symm
    _ = Nat.card (ConnectedComponents XL.left) :=
      Nat.card_congr (connectedComponentsEquivOfSchemeIso eks)
    _ = Nat.card (ConnectedComponents XKL.left) :=
      (Nat.card_congr (connectedComponentsEquivOfSchemeIso eK)).symm
    _ = Nat.card (ConnectedComponents XKKsL.left) :=
      (Nat.card_congr (connectedComponentsEquivOfSchemeIso eKs)).symm
    _ = Nat.card (ConnectedComponents XKKs.left) :=
      natCard_connectedComponents_schemeBaseChange_eq_of_isSepClosed
        (k := Ks) (K := L) XKKs

/-! ## Surjectivity over a separably closed base -/

/-- The canonical component-algebra comparison is surjective for every field
extension of a separably closed base. -/
private theorem componentBaseChangeComparisonAlgHom_surjective_of_isSepClosed
    [IsSepClosed k]
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (componentBaseChangeComparisonAlgHom (K := K) X) := by
  let P := componentSubalgebra X
  let Q := componentSubalgebra (schemeBaseChange X (L := K))
  let _ : Algebra K (P ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let f := componentBaseChangeComparisonAlgHom (K := K) X
  let _ : Module.Finite k P := (componentSubalgebra_isFiniteEtale X).1
  let _ : Module.Finite K (P ⊗[k] K) :=
    (componentAlgebraTensor_isFiniteEtale (K := K) X).1
  let _ : Module.Finite K Q :=
    (componentSubalgebra_isFiniteEtale (schemeBaseChange X (L := K))).1
  have hsource : Module.finrank K (P ⊗[k] K) = Module.finrank k P := by
    calc
      Module.finrank K (P ⊗[k] K) = Module.finrank K (K ⊗[k] P) :=
        (Algebra.TensorProduct.commRight k K P).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k P := Module.finrank_baseChange
  have hsourceComponents : Module.finrank k P =
      Nat.card (ConnectedComponents X.left) :=
    componentSubalgebra_finrank_eq_natCard_connectedComponents X
  have hle : Module.finrank K Q ≤ Module.finrank K (P ⊗[k] K) := by
    rw [hsource, hsourceComponents]
    exact componentSubalgebra_baseChange_finrank_le_of_isSepClosed (K := K) X
  have hge : Module.finrank K (P ⊗[k] K) ≤ Module.finrank K Q :=
    f.toLinearMap.finrank_le_finrank_of_injective
      (componentBaseChangeComparisonAlgHom_injective (K := K) X)
  have hfinrank : Module.finrank K (P ⊗[k] K) = Module.finrank K Q :=
    le_antisymm hge hle
  have hinjective : Function.Injective f.toLinearMap :=
    componentBaseChangeComparisonAlgHom_injective (K := K) X
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hfinrank).mp hinjective

/-! ## Arbitrary field extensions -/

/-- The canonical component-algebra comparison is surjective for every field
extension, with no algebraicity or separability assumption. -/
theorem componentBaseChangeComparisonAlgHom_surjective
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    Function.Surjective (componentBaseChangeComparisonAlgHom (K := K) X) := by
  let P := componentSubalgebra X
  let XK := schemeBaseChange X (L := K)
  let Q := componentSubalgebra XK
  let _ : Algebra K (P ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  let f := componentBaseChangeComparisonAlgHom (K := K) X
  let _ : Module.Finite k P := (componentSubalgebra_isFiniteEtale X).1
  let _ : Module.Finite K (P ⊗[k] K) :=
    (componentAlgebraTensor_isFiniteEtale (K := K) X).1
  let _ : Module.Finite K Q := (componentSubalgebra_isFiniteEtale XK).1
  have hsource : Module.finrank K (P ⊗[k] K) = Module.finrank k P := by
    calc
      Module.finrank K (P ⊗[k] K) = Module.finrank K (K ⊗[k] P) :=
        (Algebra.TensorProduct.commRight k K P).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k P := Module.finrank_baseChange
  have htarget : Module.finrank K Q = Module.finrank k P := by
    calc
      Module.finrank K Q = Nat.card (ConnectedComponents
          (schemeBaseChange XK (L := SeparableClosure K)).left) :=
        componentSubalgebra_finrank_eq_natCard_separableClosure XK
      _ = Nat.card (ConnectedComponents
          (schemeBaseChange X (L := SeparableClosure k)).left) :=
        (natCard_connectedComponents_separableClosures_eq (K := K) X).symm
      _ = Module.finrank k P :=
        (componentSubalgebra_finrank_eq_natCard_separableClosure X).symm
  have hfinrank : Module.finrank K (P ⊗[k] K) = Module.finrank K Q :=
    hsource.trans htarget.symm
  have hinjective : Function.Injective f.toLinearMap :=
    componentBaseChangeComparisonAlgHom_injective (K := K) X
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := f.toLinearMap) hfinrank).mp hinjective

/-- The reverse inclusion of component subalgebras for an
arbitrary field extension. -/
private theorem componentSubalgebra_le_baseChangedComponentSubalgebra
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra (schemeBaseChange X (L := K)) ≤
      baseChangedComponentSubalgebra (K := K) X := by
  intro y hy
  let y' : componentSubalgebra (schemeBaseChange X (L := K)) := ⟨y, hy⟩
  obtain ⟨x, hx⟩ :=
    componentBaseChangeComparisonAlgHom_surjective (K := K) X y'
  refine ⟨x, ?_⟩
  exact congrArg Subtype.val hx

/-- The scalar-extended and newly selected component subalgebras are
equal in the global-sections ring. -/
theorem baseChangedComponentSubalgebra_eq
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    baseChangedComponentSubalgebra (K := K) X =
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  le_antisymm (baseChangedComponentSubalgebra_le (K := K) X)
    (componentSubalgebra_le_baseChangedComponentSubalgebra (K := K) X)

/-- The canonical algebra equivalence for arbitrary field extension.  Its
forward map is definitionally the canonical comparison. This is the
algebraic counterpart of J. S. Milne, *Algebraic Groups* (2017),
Proposition 1.30(a). -/
noncomputable def componentBaseChangeComparisonAlgEquiv
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentSubalgebra X ⊗[k] K ≃ₐ[K]
      componentSubalgebra (schemeBaseChange X (L := K)) :=
  AlgEquiv.ofBijective (componentBaseChangeComparisonAlgHom (K := K) X)
    ⟨componentBaseChangeComparisonAlgHom_injective (K := K) X,
      componentBaseChangeComparisonAlgHom_surjective (K := K) X⟩

/-- The canonical isomorphism between the component scheme after base change
and the explicit affine tensor-product model. -/
private noncomputable def componentBaseChangeComparisonModelIso
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ≅
      componentSchemeBaseChangeModel (K := K) X :=
  specOverIsoOfAlgEquiv (componentBaseChangeComparisonAlgEquiv (K := K) X)

/-- The forward map of the model isomorphism is the canonical
comparison model. -/
private theorem componentBaseChangeComparisonModelIso_hom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (componentBaseChangeComparisonModelIso (K := K) X).hom =
      componentBaseChangeComparisonModel (K := K) X := by
  rw [componentBaseChangeComparisonModel_eq_fromAlgHom (K := K) X]
  rfl

/-- The canonical categorical base-change isomorphism for arbitrary field
extension, as in J. S. Milne, *Algebraic Groups* (2017),
Proposition 1.30(a). -/
noncomputable def componentBaseChangeIso
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    componentScheme (schemeBaseChange X (L := K)) ≅
      schemeBaseChange (componentScheme X) (L := K) :=
  (componentBaseChangeComparisonModelIso (K := K) X).trans
    (componentSchemeBaseChangeModelIso (K := K) X).symm

/-- The forward map of the categorical base-change isomorphism is exactly the
canonical `componentBaseChangeComparison`, giving the canonical map of
J. S. Milne, *Algebraic Groups* (2017), Proposition 1.30(a). -/
theorem componentBaseChangeIso_hom
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    (componentBaseChangeIso (K := K) X).hom =
      componentBaseChangeComparison (K := K) X := by
  rw [componentBaseChangeIso, Iso.trans_hom,
    componentBaseChangeComparisonModelIso_hom]
  rfl

end

end AlgebraicGeometry

#lint- only unusedArguments docBlame
