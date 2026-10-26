/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SchemeProperties.ModuleTensorAffine
public import SchemeProperties.ModuleTensorRestriction
public import Mathlib.RingTheory.Localization.Module

public section

/-!
# Tensor products of associated modules on principal affine opens

For a commutative ring `R`, `R`-modules `M` and `N`, and `f : R`, this file
compares the actual sheaf-tensor component on `D(f)` with the tensor product
over the native section ring `Γ(Spec R, D(f))`. Its inverse identifies the
restriction of top-open sections with localization of `M ⊗[R] N`.

Restriction between *any* two principal opens is semilinear over the actual
structure-sheaf restriction and is natural in both module arguments. Explicit
semilinear equivalences transport this comparison to the native
`Localization.Away f` and `LocalizedModule (.powers f)` presentations.

The principal-open proof combines the affine tensor comparison with Mathlib's
localization of `tilde` sections and tensor products; the canonical localization
maps are constructed independently of the comparison with restriction.

The statements work also for `f = 0`, `f = 1`, zero rings and zero modules;
they make no finiteness, regularity or nonemptiness assumption. They do not
identify tensor products of sections with sections of the tensor on arbitrary
opens.

## References

- Mathlib's `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` supplies the actual
  `tilde.toOpen` maps and localization of sections on basic opens.
- Mathlib's `Mathlib/RingTheory/Localization/BaseChange.lean` supplies
  `IsLocalization.moduleTensorEquiv`; its
  `Mathlib/RingTheory/Localization/Basic.lean` supplies
  `IsLocalization.algEquiv` for the Away-to-sections ring transport.
- Mathlib's `Mathlib/Algebra/Module/LocalizedModule/Basic.lean` supplies
  `IsLocalizedModule` localization uniqueness and canonical localized modules.
- `SchemeProperties.ModuleTensorAffine` and
  `SchemeProperties.ModuleTensorRestriction` supply the project affine tensor
  and open-restriction comparisons combined here.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)

private theorem affine_inv_toOpen_tmul (U : (Spec R).Opens) (m : M) (n : N) :
    ((affineTensorNatIso R).inv.app (M, N)).app U
        ((tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ[R] n)) =
      tmul (tilde M) (tilde N) U
        ((tilde.toOpen M U).hom m) ((tilde.toOpen N U).hom n) := by
  let c := (affineTensorNatIso R).inv.app (M, N)
  have hM : (tilde M).presheaf.map U.leTop.op ((tilde.toOpen M ⊤).hom m) =
      (tilde.toOpen M U).hom m := by
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (tilde.toOpen_res M ⊤ U U.leTop)) m
  have hN : (tilde N).presheaf.map U.leTop.op ((tilde.toOpen N ⊤).hom n) =
      (tilde.toOpen N U).hom n := by
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (tilde.toOpen_res N ⊤ U U.leTop)) n
  have hMN : (tilde (M ⊗ N)).presheaf.map U.leTop.op
      ((tilde.toOpen (M ⊗ N) ⊤).hom (m ⊗ₜ[R] n)) =
        (tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ[R] n) := by
    exact DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom (tilde.toOpen_res (M ⊗ N) ⊤ U U.leTop)) _
  rw [← hMN]
  have hnat := congrArg
    (fun g : Γ(tilde (M ⊗ N), ⊤) ⟶ Γ(tensor (tilde M) (tilde N), U) ↦
      g ((tilde.toOpen (M ⊗ N) ⊤).hom (m ⊗ₜ[R] n)))
    (c.mapPresheaf.naturality U.leTop.op)
  change c.app U _ = _
  change c.app U ((tilde (M ⊗ N)).presheaf.map U.leTop.op _) =
    (tensor (tilde M) (tilde N)).presheaf.map U.leTop.op (c.app ⊤ _) at hnat
  rw [hnat]
  dsimp only [c]
  rw [affineTensorNatIso_inv_app_top_tmul]
  exact (map_tmul (tilde M) (tilde N) U.leTop
    ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)).trans
      (congrArg₂ (tmul (tilde M) (tilde N) U) hM hN)

/-- The canonical `R`-linear localization map from `M ⊗[R] N` to the tensor of
associated-module sections over `Γ(Spec R, D(f))`. It uses native module
localization rather than a chosen inverse of the sheaf-tensor comparison. -/
noncomputable def locTensor (f : R) :
    TensorProduct R M N →ₗ[R]
      TensorProduct (Γ(Spec R, PrimeSpectrum.basicOpen f))
        Γ(tilde M, PrimeSpectrum.basicOpen f) Γ(tilde N, PrimeSpectrum.basicOpen f) :=
  ((IsLocalization.moduleTensorEquiv (.powers f)
    (Γ(Spec R, PrimeSpectrum.basicOpen f))
    Γ(tilde M, PrimeSpectrum.basicOpen f)
    Γ(tilde N, PrimeSpectrum.basicOpen f)).symm.restrictScalars R).toLinearMap.comp
      (TensorProduct.map (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
        (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)

theorem locTensor_tmul (f : R) (m : M) (n : N) :
    locTensor R M N f (m ⊗ₜ[R] n) =
      TensorProduct.tmul (Γ(Spec R, PrimeSpectrum.basicOpen f))
        (M := Γ(tilde M, PrimeSpectrum.basicOpen f))
        (N := Γ(tilde N, PrimeSpectrum.basicOpen f))
        ((tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom m)
        ((tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom n) := by
  rfl

/-- The native section tensor is a localization of `M ⊗[R] N` at powers of
`f`, establishing the universal-property uniqueness of `locTensor`. -/
theorem locTensor_isLocalized (f : R) :
    IsLocalizedModule (.powers f) (locTensor R M N f) := by
  unfold locTensor
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (TensorProduct.map (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom) _

private noncomputable def actualComparison (f : R) :
    TensorProduct (Γ(Spec R, PrimeSpectrum.basicOpen f))
      Γ(tilde M, PrimeSpectrum.basicOpen f) Γ(tilde N, PrimeSpectrum.basicOpen f) →ₗ[
        Γ(Spec R, PrimeSpectrum.basicOpen f)]
      Γ(tilde (M ⊗ N), PrimeSpectrum.basicOpen f) :=
  (((affineTensorNatIso R).hom.app (M, N)).val.app
    (.op (PrimeSpectrum.basicOpen f))).hom.comp
      ((tensorUnit (tilde M) (tilde N)).app (.op (PrimeSpectrum.basicOpen f))).hom

private theorem affine_hom_tmul_toOpen (U : (Spec R).Opens) (m : M) (n : N) :
    ((affineTensorNatIso R).hom.app (M, N)).app U
      (tmul (tilde M) (tilde N) U
        ((tilde.toOpen M U).hom m) ((tilde.toOpen N U).hom n)) =
      (tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ[R] n) := by
  rw [← affine_inv_toOpen_tmul]
  have h := congrArg (fun g : tilde (M ⊗ N) ⟶ tilde (M ⊗ N) ↦
    g.app U ((tilde.toOpen (M ⊗ N) U).hom (m ⊗ₜ[R] n)))
      ((affineTensorNatIso R).app (M, N)).inv_hom_id
  exact h

private theorem actualComparison_locTensor (f : R) :
    (actualComparison R M N f).restrictScalars R ∘ₗ locTensor R M N f =
      (tilde.toOpen (M ⊗ N) (PrimeSpectrum.basicOpen f)).hom := by
  ext m n
  exact affine_hom_tmul_toOpen R M N (PrimeSpectrum.basicOpen f) m n

private theorem actualComparison_bijective (f : R) :
    Function.Bijective (actualComparison R M N f) := by
  let := locTensor_isLocalized R M N f
  have hloc : IsLocalizedModule (.powers f)
      ((actualComparison R M N f).restrictScalars R ∘ₗ locTensor R M N f) := by
    rw [actualComparison_locTensor]
    exact inferInstanceAs (IsLocalizedModule.Away f
      (tilde.toOpen (M ⊗ N) (PrimeSpectrum.basicOpen f)).hom)
  have he := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp
    (.powers f) (locTensor R M N f) ((actualComparison R M N f).restrictScalars R)
  have hb : Function.Bijective (IsLocalizedModule.linearEquiv (.powers f)
      (locTensor R M N f)
      ((actualComparison R M N f).restrictScalars R ∘ₗ locTensor R M N f)).toLinearMap :=
    (IsLocalizedModule.linearEquiv (.powers f) (locTensor R M N f)
      ((actualComparison R M N f).restrictScalars R ∘ₗ locTensor R M N f)).bijective
  rw [he] at hb
  exact hb

theorem tensorUnit_basicOpen_isIso (f : R) :
    IsIso ((tensorUnit (tilde M) (tilde N)).app
      (.op (PrimeSpectrum.basicOpen f))) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let out := ((affineTensorNatIso R).hom.app (M, N)).val.app
    (.op (PrimeSpectrum.basicOpen f))
  let e := ((toPresheafOfModules (Spec R)) ⋙
    PresheafOfModules.evaluation (Spec R).ringCatSheaf.obj
      (.op (PrimeSpectrum.basicOpen f))).mapIso
      ((affineTensorNatIso R).app (M, N))
  have hout : Function.Bijective out := ConcreteCategory.bijective_of_isIso e.hom
  exact (Function.Bijective.of_comp_iff' hout _).mp
    (actualComparison_bijective R M N f)

/-- The canonical equivalence whose forward map **is** the actual `tensorUnit`
component at `D(f)`, over the native section ring `Γ(Spec R, D(f))`. -/
noncomputable def basicTensorEquiv (f : R) :
    TensorProduct (Γ(Spec R, PrimeSpectrum.basicOpen f))
      Γ(tilde M, PrimeSpectrum.basicOpen f) Γ(tilde N, PrimeSpectrum.basicOpen f) ≃ₗ[
        Γ(Spec R, PrimeSpectrum.basicOpen f)]
      Γ(tensor (tilde M) (tilde N), PrimeSpectrum.basicOpen f) :=
  letI := tensorUnit_basicOpen_isIso R M N f
  (asIso ((tensorUnit (tilde M) (tilde N)).app
    (.op (PrimeSpectrum.basicOpen f)))).toLinearEquiv

/-- The forward basic-open equivalence sends pure section tensors by the
actual `tensorUnit` component, not by an independently chosen comparison. -/
theorem basicTensorEquiv_tmul (f : R)
    (m : Γ(tilde M, PrimeSpectrum.basicOpen f))
    (n : Γ(tilde N, PrimeSpectrum.basicOpen f)) :
    basicTensorEquiv R M N f
        (m ⊗ₜ[Γ(Spec R, PrimeSpectrum.basicOpen f)] n) =
      tmul (tilde M) (tilde N) (PrimeSpectrum.basicOpen f) m n := by
  change ((tensorUnit (tilde M) (tilde N)).app
    (.op (PrimeSpectrum.basicOpen f))).hom _ = _
  exact tensorUnit_app_tmul (tilde M) (tilde N) (PrimeSpectrum.basicOpen f) m n

/-- The global affine tensor comparison, followed by the inverse of the actual
top-open `tilde.isoTop`; this takes sheaf-tensor sections to `M ⊗[R] N`. -/
noncomputable def topTensorEquiv :
    Γ(tensor (tilde M) (tilde N), ⊤) ≃ₗ[R] TensorProduct R M N :=
  ((moduleSpecΓFunctor.mapIso ((affineTensorNatIso R).app (M, N))).trans
    (tilde.isoTop (M ⊗ N)).symm).toLinearEquiv

/-- Restriction of sheaf-tensor sections from `⊤` to `D(f)`, made `R`-linear
using the native `R`-action and `map_smul_Spec`. -/
noncomputable def resTop (f : R) :
    Γ(tensor (tilde M) (tilde N), ⊤) →ₗ[R]
      Γ(tensor (tilde M) (tilde N), PrimeSpectrum.basicOpen f) where
  toFun := (tensor (tilde M) (tilde N)).presheaf.map
    (PrimeSpectrum.basicOpen f).leTop.op
  map_add' := map_add _
  map_smul' r t := map_smul_Spec (PrimeSpectrum.basicOpen f).leTop.op r t

theorem topTensorEquiv_symm_tmul (m : M) (n : N) :
    (topTensorEquiv R M N).symm (m ⊗ₜ[R] n) =
      tmul (tilde M) (tilde N) ⊤
        ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n) := by
  exact affineTensorNatIso_inv_app_top_tmul R M N m n

theorem basicTensorEquiv_locTensor (f : R) (m : M) (n : N) :
    basicTensorEquiv R M N f (locTensor R M N f (m ⊗ₜ[R] n)) =
      tmul (tilde M) (tilde N) (PrimeSpectrum.basicOpen f)
        ((tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom m)
        ((tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom n) := by
  rfl

private theorem toOpen_res_apply (L : ModuleCat.{u} R) (U : (Spec R).Opens) (l : L) :
    (tilde L).presheaf.map U.leTop.op ((tilde.toOpen L ⊤).hom l) =
      (tilde.toOpen L U).hom l :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (tilde.toOpen_res L ⊤ U U.leTop)) l

private theorem resTop_topTensorEquiv_symm (f : R) (z : TensorProduct R M N) :
    resTop R M N f ((topTensorEquiv R M N).symm z) =
      basicTensorEquiv R M N f (locTensor R M N f z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    rw [topTensorEquiv_symm_tmul, basicTensorEquiv_locTensor]
    change (tensor (tilde M) (tilde N)).presheaf.map
      (PrimeSpectrum.basicOpen f).leTop.op _ = _
    have hM := toOpen_res_apply R M (PrimeSpectrum.basicOpen f) m
    have hN := toOpen_res_apply R N (PrimeSpectrum.basicOpen f) n
    exact (map_tmul (tilde M) (tilde N) (PrimeSpectrum.basicOpen f).leTop
      ((tilde.toOpen M ⊤).hom m) ((tilde.toOpen N ⊤).hom n)).trans
        (congrArg₂ (tmul (tilde M) (tilde N) (PrimeSpectrum.basicOpen f)) hM hN)
  | add a b ha hb => simp [ha, hb]

/-- Equality of **actual** `R`-linear maps: inverse tensor-unit equivalence
after top-to-`D(f)` restriction equals native module localization after the
accepted top-open affine comparison. -/
theorem actual_restriction_square (f : R) :
    (basicTensorEquiv R M N f).symm.toLinearMap.restrictScalars R ∘ₗ
        resTop R M N f =
      locTensor R M N f ∘ₗ (topTensorEquiv R M N).toLinearMap := by
  ext t
  apply (basicTensorEquiv R M N f).injective
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.symm_apply_apply] using
    resTop_topTensorEquiv_symm R M N f (topTensorEquiv R M N t)

/-- Tensor restriction from `V` to `U` is semilinear along the actual
structure-sheaf map `Γ(Spec R, V) → Γ(Spec R, U)`. -/
@[expose]
noncomputable def sectionTensorRes {U V : (Spec R).Opens} (i : U ⟶ V) :
    TensorProduct Γ(Spec R, V) Γ(tilde M, V) Γ(tilde N, V) →ₛₗ[
      ((Spec R).presheaf.map i.op).hom]
      TensorProduct Γ(Spec R, U) Γ(tilde M, U) Γ(tilde N, U) :=
  (PresheafOfModulesOfCommRing.Monoidal.tensorObj (tilde M).val
    (tilde N).val).restrictₛₗ i.op

theorem sectionTensorRes_tmul {U V : (Spec R).Opens} (i : U ⟶ V)
    (m : Γ(tilde M, V)) (n : Γ(tilde N, V)) :
    sectionTensorRes R M N i (m ⊗ₜ[Γ(Spec R, V)] n) =
      ((tilde M).presheaf.map i.op m) ⊗ₜ[Γ(Spec R, U)]
        ((tilde N).presheaf.map i.op n) := rfl

/-- The actual tensor-unit equivalence commutes with *every* inclusion
`D(g) ≤ D(f)`, not only multiplication or divisibility inclusions. -/
theorem basicTensorEquiv_restriction {f g : R}
    (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f)
    (x : TensorProduct Γ(Spec R, PrimeSpectrum.basicOpen f)
      Γ(tilde M, PrimeSpectrum.basicOpen f) Γ(tilde N, PrimeSpectrum.basicOpen f)) :
    basicTensorEquiv R M N g (sectionTensorRes R M N i x) =
      (tensor (tilde M) (tilde N)).presheaf.map i.op
        (basicTensorEquiv R M N f x) := by
  exact PresheafOfModules.naturality_apply (tensorUnit (tilde M) (tilde N)) i.op x

theorem basicTensorEquiv_symm_restriction {f g : R}
    (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f)
    (x : Γ(tensor (tilde M) (tilde N), PrimeSpectrum.basicOpen f)) :
    (basicTensorEquiv R M N g).symm
        ((tensor (tilde M) (tilde N)).presheaf.map i.op x) =
      sectionTensorRes R M N i ((basicTensorEquiv R M N f).symm x) := by
  apply (basicTensorEquiv R M N g).injective
  rw [LinearEquiv.apply_symm_apply, basicTensorEquiv_restriction,
    LinearEquiv.apply_symm_apply]

theorem sectionTensorRes_id (U : (Spec R).Opens)
    (x : TensorProduct Γ(Spec R, U) Γ(tilde M, U) Γ(tilde N, U)) :
    sectionTensorRes R M N (𝟙 U) x = x := by
  change (PresheafOfModulesOfCommRing.Monoidal.tensorObj (tilde M).val
    (tilde N).val).map (𝟙 (.op U)) x = x
  simp

theorem sectionTensorRes_comp {U V W : (Spec R).Opens} (i : U ⟶ V) (j : V ⟶ W)
    (x : TensorProduct Γ(Spec R, W) Γ(tilde M, W) Γ(tilde N, W)) :
    sectionTensorRes R M N (i ≫ j) x =
      sectionTensorRes R M N i (sectionTensorRes R M N j x) := by
  exact PresheafOfModules.map_comp_apply
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (tilde M).val (tilde N).val)
    j.op i.op x

theorem sectionTensorRes_locTensor {f g : R}
    (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f)
    (m : M) (n : N) :
    sectionTensorRes R M N i (locTensor R M N f (m ⊗ₜ[R] n)) =
      locTensor R M N g (m ⊗ₜ[R] n) := by
  rw [locTensor_tmul, sectionTensorRes_tmul, locTensor_tmul]
  have hM := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (tilde.toOpen_res M (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) i)) m
  have hN := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (tilde.toOpen_res N (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) i)) n
  exact congrArg₂
    (TensorProduct.tmul Γ(Spec R, PrimeSpectrum.basicOpen g)
      (M := Γ(tilde M, PrimeSpectrum.basicOpen g))
      (N := Γ(tilde N, PrimeSpectrum.basicOpen g))) hM hN

theorem sectionTensorRes_locTensor_apply {f g : R}
    (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f)
    (x : TensorProduct R M N) :
    sectionTensorRes R M N i (locTensor R M N f x) = locTensor R M N g x := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact sectionTensorRes_locTensor R M N i m n
  | add x y hx hy => simp only [map_add, hx, hy]

theorem basicTensorEquiv_restriction_square {f g : R}
    (i : PrimeSpectrum.basicOpen g ⟶ PrimeSpectrum.basicOpen f) :
    (basicTensorEquiv R M N g).symm.toLinearMap.comp
        ((tensor (tilde M) (tilde N)).val.restrictₛₗ i.op) =
      (sectionTensorRes R M N i).comp
        (basicTensorEquiv R M N f).symm.toLinearMap := by
  ext x
  exact basicTensorEquiv_symm_restriction R M N i x

theorem basicTensorEquiv_product_paths (f g : R)
    (x : Γ(tensor (tilde M) (tilde N), ⊤)) :
    sectionTensorRes R M N (homOfLE (PrimeSpectrum.basicOpen_mul_le_left f g))
        ((basicTensorEquiv R M N f).symm (resTop R M N f x)) =
      sectionTensorRes R M N (homOfLE (PrimeSpectrum.basicOpen_mul_le_right f g))
        ((basicTensorEquiv R M N g).symm (resTop R M N g x)) := by
  rw [← basicTensorEquiv_symm_restriction, ← basicTensorEquiv_symm_restriction]
  congr 1
  change (tensor (tilde M) (tilde N)).presheaf.map _
    ((tensor (tilde M) (tilde N)).presheaf.map _ x) =
    (tensor (tilde M) (tilde N)).presheaf.map _
      ((tensor (tilde M) (tilde N)).presheaf.map _ x)
  rw [← (tensor (tilde M) (tilde N)).presheaf.map_comp_apply,
    ← (tensor (tilde M) (tilde N)).presheaf.map_comp_apply]
  rfl

/-- The canonical basic-open comparison is natural in both module maps. -/
theorem basicTensorEquiv_naturality {M' N' : ModuleCat.{u} R}
    (a : M ⟶ M') (b : N ⟶ N') (f : R)
    (x : TensorProduct Γ(Spec R, PrimeSpectrum.basicOpen f)
      Γ(tilde M, PrimeSpectrum.basicOpen f) Γ(tilde N, PrimeSpectrum.basicOpen f)) :
    basicTensorEquiv R M' N' f
        (TensorProduct.map ((tilde.map a).val.app (.op (PrimeSpectrum.basicOpen f))).hom
          ((tilde.map b).val.app (.op (PrimeSpectrum.basicOpen f))).hom x) =
      ((tensorFunctor (Spec R)).map (tilde.map a, tilde.map b)).app
        (PrimeSpectrum.basicOpen f) (basicTensorEquiv R M N f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    exact (tensorFunctor_map_app_tmul (tilde.map a) (tilde.map b)
      (PrimeSpectrum.basicOpen f) m n).symm
  | add x y hx hy =>
    simp only [map_add, hx, hy]

private instance awayRingHomInvPair (f : R) :
    RingHomInvPair
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv
    (IsLocalization.algEquiv (.powers f) (Localization.Away f)
      Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv

private instance awayRingHomInvPair_symm (f : R) :
    RingHomInvPair
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm
    (IsLocalization.algEquiv (.powers f) (Localization.Away f)
      Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv

private theorem away_smul_eq_native (L : ModuleCat.{u} R) (f : R)
    (r : Localization.Away f) (x : LocalizedModule (.powers f) L) :
    letI : Module Γ(Spec R, PrimeSpectrum.basicOpen f)
      (LocalizedModule (.powers f) L) := LocalizedModule.moduleOfIsLocalization
    r • x = IsLocalization.algEquiv (.powers f) (Localization.Away f)
      Γ(Spec R, PrimeSpectrum.basicOpen f) r • x := by
  let : Module Γ(Spec R, PrimeSpectrum.basicOpen f)
      (LocalizedModule (.powers f) L) := LocalizedModule.moduleOfIsLocalization
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (.powers f) r
  induction x using LocalizedModule.induction_on with
  | h m t =>
    rw [IsLocalization.algEquiv_mk']
    rw [← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk,
      LocalizedModule.mk'_smul_mk]

/-- Canonical equivalence from the localized module over `Localization.Away f`
to native sections on `D(f)`. It is semilinear over the native
`IsLocalization.algEquiv` from `Away f` to `Γ(Spec R, D(f))`. -/
noncomputable def awayModuleEquiv (L : ModuleCat.{u} R) (f : R) :
    letI : RingHomInvPair
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom :=
      RingHomInvPair.of_ringEquiv
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv
    letI : RingHomInvPair
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv
    LinearEquiv (σ' := (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom)
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
      (LocalizedModule (.powers f) L) Γ(tilde L, PrimeSpectrum.basicOpen f) := by
  letI : Module Γ(Spec R, PrimeSpectrum.basicOpen f)
      (LocalizedModule (.powers f) L) := LocalizedModule.moduleOfIsLocalization
  let e₀ := IsLocalizedModule.iso (.powers f)
    (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom
  let e : LocalizedModule (.powers f) L ≃ₗ[R] Γ(tilde L, PrimeSpectrum.basicOpen f) := e₀
  let eS := e.extendScalarsOfIsLocalization (.powers f)
    Γ(Spec R, PrimeSpectrum.basicOpen f)
  exact
    { e.toAddEquiv with
      map_smul' := fun r x ↦ by
        change eS (r • x) = IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f) r • eS x
        rw [away_smul_eq_native R L f r x, eS.map_smul] }

theorem awayModuleEquiv_mk (L : ModuleCat.{u} R) (f : R) (m : L) :
    awayModuleEquiv R L f (LocalizedModule.mk m 1) =
      (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom m := by
  exact IsLocalizedModule.iso_mk_one (.powers f)
    (tilde.toOpen L (PrimeSpectrum.basicOpen f)).hom m

/-- The semilinear comparison from the tensor of explicit localized modules
over `Localization.Away f` to the tensor of native sections over
`Γ(Spec R, D(f))`, along the native `IsLocalization.algEquiv`. -/
noncomputable def awayTensorEquiv (f : R) :
    letI : RingHomInvPair
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom :=
      RingHomInvPair.of_ringEquiv
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv
    letI : RingHomInvPair
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom :=
      RingHomInvPair.of_ringEquiv_symm
        (IsLocalization.algEquiv (.powers f) (Localization.Away f)
          Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv
    LinearEquiv (σ' := (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).symm.toRingEquiv.toRingHom)
      (IsLocalization.algEquiv (.powers f) (Localization.Away f)
        Γ(Spec R, PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom
      (TensorProduct (Localization.Away f)
        (LocalizedModule (.powers f) M) (LocalizedModule (.powers f) N))
      (TensorProduct Γ(Spec R, PrimeSpectrum.basicOpen f)
        Γ(tilde M, PrimeSpectrum.basicOpen f) Γ(tilde N, PrimeSpectrum.basicOpen f)) :=
  TensorProduct.congr (awayModuleEquiv R M f) (awayModuleEquiv R N f)

theorem awayTensorEquiv_mk_tmul (f : R) (m : M) (n : N) :
    awayTensorEquiv R M N f
        (LocalizedModule.mk m 1 ⊗ₜ[Localization.Away f] LocalizedModule.mk n 1) =
      locTensor R M N f (m ⊗ₜ[R] n) := by
  change awayModuleEquiv R M f (LocalizedModule.mk m 1) ⊗ₜ[_]
    awayModuleEquiv R N f (LocalizedModule.mk n 1) = _
  rw [awayModuleEquiv_mk, awayModuleEquiv_mk, locTensor_tmul]

/-- Canonical `R`-linear tensor localization in the explicit `Away f`
presentation, built from native `LocalizedModule.mkLinearMap` and
`IsLocalization.moduleTensorEquiv`, independently of the restriction square. -/
@[expose]
noncomputable def awayLocTensor (f : R) :
    TensorProduct R M N →ₗ[R]
      TensorProduct (Localization.Away f)
        (LocalizedModule (.powers f) M) (LocalizedModule (.powers f) N) :=
  ((IsLocalization.moduleTensorEquiv (.powers f) (Localization.Away f)
    (LocalizedModule (.powers f) M) (LocalizedModule (.powers f) N)
      ).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.map (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap (.powers f) N))

theorem awayLocTensor_tmul (f : R) (m : M) (n : N) :
    awayLocTensor R M N f (m ⊗ₜ[R] n) =
      LocalizedModule.mk m 1 ⊗ₜ[Localization.Away f] LocalizedModule.mk n 1 := rfl

/-- The explicit Away tensor localization has the native module-localization
universal property, in addition to its pure-tensor generator law. -/
theorem awayLocTensor_isLocalized (f : R) :
    IsLocalizedModule (.powers f) (awayLocTensor R M N f) := by
  unfold awayLocTensor
  exact IsLocalizedModule.of_linearEquiv (.powers f)
    (TensorProduct.map (LocalizedModule.mkLinearMap (.powers f) M)
      (LocalizedModule.mkLinearMap (.powers f) N)) _

theorem awayTensorEquiv_awayLocTensor (f : R) (x : TensorProduct R M N) :
    awayTensorEquiv R M N f (awayLocTensor R M N f x) = locTensor R M N f x := by
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact awayTensorEquiv_mk_tmul R M N f m n
  | add x y hx hy => simp only [map_add, hx, hy]

theorem away_actual_restriction_square (f : R)
    (x : Γ(tensor (tilde M) (tilde N), ⊤)) :
    (awayTensorEquiv R M N f).symm
        ((basicTensorEquiv R M N f).symm (resTop R M N f x)) =
      awayLocTensor R M N f (topTensorEquiv R M N x) := by
  apply (awayTensorEquiv R M N f).injective
  rw [LinearEquiv.apply_symm_apply, awayTensorEquiv_awayLocTensor]
  exact DFunLike.congr_fun (actual_restriction_square R M N f) x

end AlgebraicGeometry.Scheme.Modules
