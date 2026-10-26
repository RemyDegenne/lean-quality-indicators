/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

public section

/-!
# Tensor products of presheaf-module stalks

A tensor product of presheaves of modules commutes with taking stalks at a supplied
point. The comparison uses the existing module structures over the ring stalk.
It applies to arbitrary presheaves over an arbitrary topological space and is
natural in both module arguments; no sheaf or finiteness assumption is needed.

The comparison is constructed here using Mathlib's filtered module-colimit
structures and pointwise presheaf tensor product.

## References

- Mathlib's `Mathlib/Algebra/Category/ModuleCat/Presheaf/ColimitFunctor.lean`
  supplies module colimits and common-representative lemmas used at the stalk.
- Mathlib's `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` and
  `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` supply the stalk
  scalar/germ operations and pointwise presheaf tensor product.
-/


open CategoryTheory MonoidalCategory TopologicalSpace Opposite

universe u

namespace PresheafOfModulesOfCommRing

variable {X : TopCat.{u}} (A : X.Presheaf CommRingCat.{u})
  (P Q : PresheafOfModulesOfCommRing.{u} A) (x : X)

private noncomputable abbrev PStalk := TopCat.Presheaf.stalk P.presheaf x
private noncomputable abbrev QStalk := TopCat.Presheaf.stalk Q.presheaf x


private noncomputable abbrev ADiag : (OpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
  (OpenNhds.inclusion x).op ⋙ A

private noncomputable abbrev PDiag : PresheafOfModulesOfCommRing.{u} (ADiag A x) :=
  (PresheafOfModulesOfCommRing.pushforward₀ (OpenNhds.inclusion x) A).obj P

private noncomputable abbrev QDiag : PresheafOfModulesOfCommRing.{u} (ADiag A x) :=
  (PresheafOfModulesOfCommRing.pushforward₀ (OpenNhds.inclusion x) A).obj Q

private noncomputable abbrev cA : Limits.Cocone (ADiag A x ⋙ forget₂ CommRingCat RingCat) :=
  (forget₂ CommRingCat RingCat).mapCocone (Limits.colimit.cocone (ADiag A x))

private noncomputable abbrev hcA : Limits.IsColimit (cA A x) :=
  Limits.isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (Limits.colimit.isColimit (ADiag A x))

private noncomputable abbrev cP : Limits.Cocone (PDiag A P x).presheaf :=
  Limits.colimit.cocone (PDiag A P x).presheaf

private noncomputable abbrev hcP : Limits.IsColimit (cP A P x) :=
  Limits.colimit.isColimit (PDiag A P x).presheaf

private noncomputable abbrev cQ : Limits.Cocone (QDiag A Q x).presheaf :=
  Limits.colimit.cocone (QDiag A Q x).presheaf

private noncomputable abbrev hcQ : Limits.IsColimit (cQ A Q x) :=
  Limits.colimit.isColimit (QDiag A Q x).presheaf

private noncomputable abbrev TDiag : PresheafOfModulesOfCommRing.{u} (ADiag A x) :=
  PDiag A P x ⊗ QDiag A Q x

private noncomputable abbrev cT : Limits.Cocone (TDiag A P Q x).presheaf :=
  Limits.colimit.cocone (TDiag A P Q x).presheaf

private noncomputable abbrev hcT : Limits.IsColimit (cT A P Q x) :=
  Limits.colimit.isColimit (TDiag A P Q x).presheaf

private noncomputable abbrev MC (M : PresheafOfModulesOfCommRing.{u} A) :=
  PresheafOfModules.ModuleColimit (hcA A x)
    (Limits.colimit.isColimit
      ((PresheafOfModulesOfCommRing.pushforward₀ (OpenNhds.inclusion x) A).obj M).presheaf)

private noncomputable abbrev MCT :=
  PresheafOfModules.ModuleColimit (hcA A x) (hcT A P Q x)

private noncomputable local instance openNhdsInitiallySmall : InitiallySmall.{u} (OpenNhds x) :=
  initiallySmall_of_essentiallySmall _

private noncomputable local instance colimitCommRing : CommRing ((cA A x).pt) :=
  inferInstanceAs (CommRing (A.stalk x))

private structure CommonRep (m : MC A x P) (n : MC A x Q) where
  U : (OpenNhds x)ᵒᵖ
  p : (PDiag A P x).obj U
  q : (QDiag A Q x).obj U
  hp : PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcP A P x) p = m
  hq : PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcQ A Q x) q = n

private noncomputable def commonRep (m : MC A x P) (n : MC A x Q) :
    CommonRep A P Q x m n :=
  Classical.choice (show Nonempty (CommonRep A P Q x m n) from by
    obtain ⟨U, p, q, hp, hq⟩ :=
      PresheafOfModules.ModuleColimit.ιM_jointly_surjective₂ m n
    exact Nonempty.intro { U := U, p := p, q := q, hp := hp, hq := hq })

private noncomputable def backwardSet (m : MC A x P) (n : MC A x Q) :
    MCT A P Q x :=
  PresheafOfModules.ModuleColimit.ιM
    (hcR := hcA A x) (hcM := hcT A P Q x)
    ((commonRep A P Q x m n).p ⊗ₜ (commonRep A P Q x m n).q)

private theorem backwardSet_of_rep (U : (OpenNhds x)ᵒᵖ) (p : (PDiag A P x).obj U)
    (q : (QDiag A Q x).obj U) :
    backwardSet A P Q x
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcA A x) (hcM := hcP A P x) p)
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcA A x) (hcM := hcQ A Q x) q) =
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) (p ⊗ₜ q) := by
  let c := commonRep A P Q x
    (PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcP A P x) p)
    (PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcQ A Q x) q)
  obtain ⟨UP, fP, gP, hP⟩ := (hcP A P x).eq_iff.mp c.hp
  obtain ⟨UQ, fQ, gQ, hQ⟩ := (hcQ A Q x).eq_iff.mp c.hq
  let W := IsFiltered.max UP UQ
  let iP : UP ⟶ W := IsFiltered.leftToMax UP UQ
  let iQ : UQ ⟶ W := IsFiltered.rightToMax UP UQ
  let aP : c.U ⟶ W := fP ≫ iP
  let aQ : c.U ⟶ W := fQ ≫ iQ
  let W₁ := IsFiltered.coeq aP aQ
  let e₁ : W ⟶ W₁ := IsFiltered.coeqHom aP aQ
  have ha : aP ≫ e₁ = aQ ≫ e₁ := IsFiltered.coeq_condition aP aQ
  let bP : U ⟶ W₁ := gP ≫ iP ≫ e₁
  let bQ : U ⟶ W₁ := gQ ≫ iQ ≫ e₁
  let Z := IsFiltered.coeq bP bQ
  let e₂ : W₁ ⟶ Z := IsFiltered.coeqHom bP bQ
  have hb : bP ≫ e₂ = bQ ≫ e₂ := IsFiltered.coeq_condition bP bQ
  let F : c.U ⟶ Z := fP ≫ (iP ≫ (e₁ ≫ e₂))
  let G : U ⟶ Z := gP ≫ (iP ≫ (e₁ ≫ e₂))
  have hFQ : F = fQ ≫ (iQ ≫ (e₁ ≫ e₂)) := by
    have := congrArg (fun k ↦ k ≫ e₂) ha
    simpa [F, aP, aQ, Category.assoc] using this
  have hGQ : G = gQ ≫ (iQ ≫ (e₁ ≫ e₂)) := by
    simpa [G, bP, bQ, Category.assoc] using hb
  have hPZ : (PDiag A P x).presheaf.map F c.p =
      (PDiag A P x).presheaf.map G p := by
    let kP := iP ≫ (e₁ ≫ e₂)
    calc
      _ = (PDiag A P x).presheaf.map kP
          ((PDiag A P x).presheaf.map fP c.p) := by
        dsimp [F, kP]
        have hh := ConcreteCategory.congr_hom
          ((PDiag A P x).presheaf.map_comp fP (iP ≫ (e₁ ≫ e₂))) c.p
        erw [ConcreteCategory.comp_apply] at hh
        exact hh
      _ = (PDiag A P x).presheaf.map kP
          ((PDiag A P x).presheaf.map gP p) := congrArg _ hP
      _ = _ := by
        dsimp [G, kP]
        have hh := ConcreteCategory.congr_hom
          ((PDiag A P x).presheaf.map_comp gP (iP ≫ (e₁ ≫ e₂))) p
        erw [ConcreteCategory.comp_apply] at hh
        exact hh.symm
  have hQZ : (QDiag A Q x).presheaf.map F c.q =
      (QDiag A Q x).presheaf.map G q := by
    rw [hFQ, hGQ]
    let kQ := iQ ≫ (e₁ ≫ e₂)
    calc
      _ = (QDiag A Q x).presheaf.map kQ
          ((QDiag A Q x).presheaf.map fQ c.q) := by
        dsimp [kQ]
        have hh := ConcreteCategory.congr_hom
          ((QDiag A Q x).presheaf.map_comp fQ (iQ ≫ (e₁ ≫ e₂))) c.q
        erw [ConcreteCategory.comp_apply] at hh
        exact hh
      _ = (QDiag A Q x).presheaf.map kQ
          ((QDiag A Q x).presheaf.map gQ q) := congrArg _ hQ
      _ = _ := by
        dsimp [kQ]
        have hh := ConcreteCategory.congr_hom
          ((QDiag A Q x).presheaf.map_comp gQ (iQ ≫ (e₁ ≫ e₂))) q
        erw [ConcreteCategory.comp_apply] at hh
        exact hh.symm
  apply (hcT A P Q x).eq_iff.mpr
  refine ⟨Z, F, G, ?_⟩
  change
    (TDiag A P Q x).map F
        (show (TDiag A P Q x).obj c.U from c.p ⊗ₜ c.q) =
      (TDiag A P Q x).map G
        (show (TDiag A P Q x).obj U from p ⊗ₜ q)
  rw [show (TDiag A P Q x).map F
        (show (TDiag A P Q x).obj c.U from c.p ⊗ₜ c.q) =
      (PDiag A P x).map F c.p ⊗ₜ (QDiag A Q x).map F c.q from
    PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul F c.p c.q]
  rw [show (TDiag A P Q x).map G
        (show (TDiag A P Q x).obj U from p ⊗ₜ q) =
      (PDiag A P x).map G p ⊗ₜ (QDiag A Q x).map G q from
    PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul G p q]
  erw [hPZ, hQZ]
  rfl

private theorem backwardSet_add_left (m₁ m₂ : MC A x P) (n : MC A x Q) :
    backwardSet A P Q x (m₁ + m₂) n =
      backwardSet A P Q x m₁ n + backwardSet A P Q x m₂ n := by
  obtain ⟨U, p₁, p₂, q, rfl, rfl, rfl⟩ :=
    PresheafOfModules.ModuleColimit.ιM_jointly_surjective₃ m₁ m₂ n
  rw [← map_add, backwardSet_of_rep, backwardSet_of_rep, backwardSet_of_rep]
  let t₁ : (TDiag A P Q x).obj U := p₁ ⊗ₜ q
  let t₂ : (TDiag A P Q x).obj U := p₂ ⊗ₜ q
  change PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcT A P Q x)
        (show (TDiag A P Q x).obj U from (p₁ + p₂) ⊗ₜ q) =
    PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) t₁ +
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) t₂
  rw [show (show (TDiag A P Q x).obj U from (p₁ + p₂) ⊗ₜ q) = t₁ + t₂ from
    TensorProduct.add_tmul p₁ p₂ q, map_add]

private theorem backwardSet_add_right (m : MC A x P) (n₁ n₂ : MC A x Q) :
    backwardSet A P Q x m (n₁ + n₂) =
      backwardSet A P Q x m n₁ + backwardSet A P Q x m n₂ := by
  obtain ⟨U, p, q₁, q₂, rfl, rfl, rfl⟩ :=
    PresheafOfModules.ModuleColimit.ιM_jointly_surjective₃ m n₁ n₂
  rw [← map_add, backwardSet_of_rep, backwardSet_of_rep, backwardSet_of_rep]
  let t₁ : (TDiag A P Q x).obj U := p ⊗ₜ q₁
  let t₂ : (TDiag A P Q x).obj U := p ⊗ₜ q₂
  change PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcT A P Q x)
        (show (TDiag A P Q x).obj U from p ⊗ₜ (q₁ + q₂)) =
    PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) t₁ +
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) t₂
  rw [show (show (TDiag A P Q x).obj U from p ⊗ₜ (q₁ + q₂)) = t₁ + t₂ from
    TensorProduct.tmul_add p q₁ q₂, map_add]

private theorem backwardSet_smul_left (r : (cA A x).pt) (m : MC A x P) (n : MC A x Q) :
    backwardSet A P Q x (r • m) n = r • backwardSet A P Q x m n := by
  obtain ⟨U, a, p, q, rfl, rfl, rfl⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₃' r m n
  rw [PresheafOfModules.ModuleColimit.smul_eq, backwardSet_of_rep,
    backwardSet_of_rep]
  let t : (TDiag A P Q x).obj U := p ⊗ₜ q
  let ta : (TDiag A P Q x).obj U := (a • p) ⊗ₜ q
  change PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcT A P Q x) ta =
    (PresheafOfModules.ModuleColimit.ιR (cA A x)) a •
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) t
  rw [PresheafOfModules.ModuleColimit.smul_eq]
  congr 1

private theorem backwardSet_smul_right (r : (cA A x).pt) (m : MC A x P) (n : MC A x Q) :
    backwardSet A P Q x m (r • n) = r • backwardSet A P Q x m n := by
  obtain ⟨U, a, p, q, rfl, rfl, rfl⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₃' r m n
  rw [PresheafOfModules.ModuleColimit.smul_eq, backwardSet_of_rep,
    backwardSet_of_rep]
  let t : (TDiag A P Q x).obj U := p ⊗ₜ q
  let ta : (TDiag A P Q x).obj U := p ⊗ₜ (a • q)
  change PresheafOfModules.ModuleColimit.ιM
      (hcR := hcA A x) (hcM := hcT A P Q x) ta =
    (PresheafOfModules.ModuleColimit.ιR (cA A x)) a •
      PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) t
  rw [PresheafOfModules.ModuleColimit.smul_eq]
  congr 1
  let a' : (ADiag A x).obj U := a
  change p ⊗ₜ[(ADiag A x).obj U] (a' • q) = a' • (p ⊗ₜ[(ADiag A x).obj U] q)
  exact TensorProduct.tmul_smul a' p q

private noncomputable abbrev NativeTensor :=
  TensorProduct (A.stalk x) (PStalk A P x) (QStalk A Q x)

private noncomputable def nativeRingGerm (U : (OpenNhds x)ᵒᵖ)
    (a : (ADiag A x).obj U) : A.stalk x :=
  PresheafOfModules.ModuleColimit.ιR (cA A x) a

private noncomputable def nativeModuleGerm
    (M : PresheafOfModulesOfCommRing.{u} A) (U : (OpenNhds x)ᵒᵖ)
    (m : (PDiag A M x).obj U) : PStalk A M x :=
  PresheafOfModules.ModuleColimit.ιM
    (hcR := hcA A x) (hcM := hcP A M x) m

private theorem nativeModuleGerm_smul
    (M : PresheafOfModulesOfCommRing.{u} A) (U : (OpenNhds x)ᵒᵖ)
    (a : (ADiag A x).obj U) (m : (PDiag A M x).obj U) :
    nativeModuleGerm A x M U (a • m) =
      nativeRingGerm A x U a • nativeModuleGerm A x M U m := by
  exact PresheafOfModules.germ_smul M x U.unop.1 U.unop.2 a m

private theorem nativeModuleGerm_map
    (M : PresheafOfModulesOfCommRing.{u} A) {U V : (OpenNhds x)ᵒᵖ}
    (f : U ⟶ V) (m : (PDiag A M x).obj U) :
    nativeModuleGerm A x M V ((PDiag A M x).map f m) =
      nativeModuleGerm A x M U m := by
  exact ConcreteCategory.congr_hom ((cP A M x).w f) m

private theorem nativeModuleGerm_add
    (M : PresheafOfModulesOfCommRing.{u} A) (U : (OpenNhds x)ᵒᵖ)
    (m n : (PDiag A M x).obj U) :
    nativeModuleGerm A x M U (m + n) =
      nativeModuleGerm A x M U m + nativeModuleGerm A x M U n := by
  exact map_add ((cP A M x).ι.app U).hom m n

private noncomputable def nativeTensorGerm (U : (OpenNhds x)ᵒᵖ)
    (t : (TDiag A P Q x).obj U) : PStalk A (P ⊗ Q) x :=
  PresheafOfModules.ModuleColimit.ιM
    (hcR := hcA A x) (hcM := hcT A P Q x) t

private theorem nativeTensorGerm_smul (U : (OpenNhds x)ᵒᵖ)
    (a : (ADiag A x).obj U) (t : (TDiag A P Q x).obj U) :
    nativeTensorGerm A P Q x U (a • t) =
      nativeRingGerm A x U a • nativeTensorGerm A P Q x U t := by
  exact PresheafOfModules.germ_smul (P ⊗ Q) x U.unop.1 U.unop.2 a t

private theorem nativeTensorGerm_add (U : (OpenNhds x)ᵒᵖ)
    (s t : (TDiag A P Q x).obj U) :
    nativeTensorGerm A P Q x U (s + t) =
      nativeTensorGerm A P Q x U s + nativeTensorGerm A P Q x U t := by
  exact map_add ((cT A P Q x).ι.app U).hom s t

private noncomputable def stageTensorToNative (U : (OpenNhds x)ᵒᵖ) :
    (TDiag A P Q x).obj U ⟶
      (ModuleCat.restrictScalars
        ((Limits.colimit.cocone (ADiag A x)).ι.app U).hom).obj
          (ModuleCat.of (A.stalk x) (NativeTensor A P Q x)) :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun p q ↦
      nativeModuleGerm A x P U p ⊗ₜ[A.stalk x]
        nativeModuleGerm A x Q U q)
    (by
      intros
      rw [nativeModuleGerm_add, TensorProduct.add_tmul]
      rfl)
    (by
      intro r p q
      rw [nativeModuleGerm_smul]
      change _ = nativeRingGerm A x U r • (_ ⊗ₜ _)
      exact (TensorProduct.smul_tmul' _ _ _).symm)
    (by
      intros
      rw [nativeModuleGerm_add, TensorProduct.tmul_add]
      rfl)
    (by
      intro r p q
      rw [nativeModuleGerm_smul]
      rw [TensorProduct.tmul_smul]
      change _ = nativeRingGerm A x U r • (_ ⊗ₜ _)
      rfl)

private noncomputable def tensorToNativeAbNat :
    (TDiag A P Q x).presheaf ⟶
      (Functor.const _).obj (AddCommGrpCat.of (NativeTensor A P Q x)) where
  app U := AddCommGrpCat.ofHom (stageTensorToNative A P Q x U).hom.toAddMonoidHom
  naturality {U V} f := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul p q =>
        change
          (stageTensorToNative A P Q x V).hom
              ((TDiag A P Q x).map f (p ⊗ₜ q)) =
            (stageTensorToNative A P Q x U).hom (p ⊗ₜ q)
        change
          nativeModuleGerm A x P V ((PDiag A P x).map f p) ⊗ₜ[A.stalk x]
              nativeModuleGerm A x Q V ((QDiag A Q x).map f q) =
            nativeModuleGerm A x P U p ⊗ₜ[A.stalk x]
              nativeModuleGerm A x Q U q
        rw [nativeModuleGerm_map, nativeModuleGerm_map]
    | add s t hs ht =>
        let L : (TDiag A P Q x).obj U →+ NativeTensor A P Q x :=
          ((TDiag A P Q x).presheaf.map f ≫
            AddCommGrpCat.ofHom
              (stageTensorToNative A P Q x V).hom.toAddMonoidHom).hom
        let R : (TDiag A P Q x).obj U →+ NativeTensor A P Q x :=
          (AddCommGrpCat.ofHom
            (stageTensorToNative A P Q x U).hom.toAddMonoidHom).hom
        have hs' : L s = R s := hs
        have ht' : L t = R t := ht
        change L (s + t) = R (s + t)
        calc
          _ = L s + L t := map_add L s t
          _ = R s + R t := congrArg₂ (fun a b ↦ a + b) hs' ht'
          _ = _ := (map_add R s t).symm

private noncomputable def nativeCocone :
    Limits.Cocone (TDiag A P Q x).presheaf where
  pt := AddCommGrpCat.of (NativeTensor A P Q x)
  ι := tensorToNativeAbNat A P Q x

private noncomputable def forwardNativeAdd :
    PStalk A (P ⊗ Q) x →+ NativeTensor A P Q x :=
  (hcT A P Q x).desc (nativeCocone A P Q x) |>.hom

private theorem forwardNativeAdd_ι (U : (OpenNhds x)ᵒᵖ) (t : (TDiag A P Q x).obj U) :
    forwardNativeAdd A P Q x
        (PresheafOfModules.ModuleColimit.ιM
          (hcR := hcA A x) (hcM := hcT A P Q x) t) =
      (stageTensorToNative A P Q x U).hom t := by
  exact ConcreteCategory.congr_hom
    ((hcT A P Q x).fac (nativeCocone A P Q x) U) t

private theorem forwardNativeAdd_tmul (U : (OpenNhds x)ᵒᵖ)
    (p : (PDiag A P x).obj U) (q : (QDiag A Q x).obj U) :
    forwardNativeAdd A P Q x
        (nativeTensorGerm A P Q x U (p ⊗ₜ q)) =
      nativeModuleGerm A x P U p ⊗ₜ[A.stalk x]
        nativeModuleGerm A x Q U q := by
  change forwardNativeAdd A P Q x
      (PresheafOfModules.ModuleColimit.ιM
        (hcR := hcA A x) (hcM := hcT A P Q x) (p ⊗ₜ q)) = _
  exact forwardNativeAdd_ι A P Q x U (p ⊗ₜ q)

private noncomputable def forwardNative :
    PStalk A (P ⊗ Q) x →ₗ[A.stalk x] NativeTensor A P Q x where
  toFun := forwardNativeAdd A P Q x
  map_add' := map_add (forwardNativeAdd A P Q x)
  map_smul' r z := by
    obtain ⟨U, a, t, hr, hz⟩ :=
      PresheafOfModules.ModuleColimit.jointly_surjective₂
        (hcR := hcA A x) (hcM := hcT A P Q x) r z
    have hr' : nativeRingGerm A x U a = r := hr
    have hz' : nativeTensorGerm A P Q x U t = z := hz
    rw [← hr', ← hz', ← nativeTensorGerm_smul A P Q x U a t]
    rw [show forwardNativeAdd A P Q x (nativeTensorGerm A P Q x U (a • t)) =
        (stageTensorToNative A P Q x U).hom (a • t) from
      forwardNativeAdd_ι A P Q x U (a • t)]
    rw [show forwardNativeAdd A P Q x (nativeTensorGerm A P Q x U t) =
        (stageTensorToNative A P Q x U).hom t from
      forwardNativeAdd_ι A P Q x U t]
    let a' : (ADiag A x).obj U := a
    change (stageTensorToNative A P Q x U).hom (a' • t) =
      nativeRingGerm A x U a' •
        (show NativeTensor A P Q x from (stageTensorToNative A P Q x U).hom t)
    have h := map_smul (stageTensorToNative A P Q x U).hom a' t
    exact h

private noncomputable def backwardSetNative
    (m : PStalk A P x) (n : PStalk A Q x) : PStalk A (P ⊗ Q) x :=
  backwardSet A P Q x m n

private theorem backwardSetNative_of_germ (U : (OpenNhds x)ᵒᵖ)
    (p : (PDiag A P x).obj U) (q : (QDiag A Q x).obj U) :
    backwardSetNative A P Q x
        (nativeModuleGerm A x P U p) (nativeModuleGerm A x Q U q) =
      nativeTensorGerm A P Q x U (p ⊗ₜ q) := by
  exact backwardSet_of_rep A P Q x U p q

private theorem backwardSetNative_add_left (m₁ m₂ : PStalk A P x) (n : PStalk A Q x) :
    backwardSetNative A P Q x (m₁ + m₂) n =
      backwardSetNative A P Q x m₁ n + backwardSetNative A P Q x m₂ n := by
  exact backwardSet_add_left A P Q x m₁ m₂ n

private theorem backwardSetNative_add_right (m : PStalk A P x) (n₁ n₂ : PStalk A Q x) :
    backwardSetNative A P Q x m (n₁ + n₂) =
      backwardSetNative A P Q x m n₁ + backwardSetNative A P Q x m n₂ := by
  exact backwardSet_add_right A P Q x m n₁ n₂

private theorem backwardSet_smul_left_native (r : A.stalk x)
    (m : PStalk A P x) (n : PStalk A Q x) :
    backwardSetNative A P Q x (r • m) n = r • backwardSetNative A P Q x m n := by
  obtain ⟨U, a, p, q, hr, hm, hn⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₃'
      (hcR := hcA A x) (hcM := hcP A P x) (hcM' := hcQ A Q x) r m n
  have hr' : nativeRingGerm A x U a = r := hr
  have hm' : nativeModuleGerm A x P U p = m := hm
  have hn' : nativeModuleGerm A x Q U q = n := hn
  rw [← hr', ← hm', ← hn',
    ← nativeModuleGerm_smul A x P U a p,
    backwardSetNative_of_germ, backwardSetNative_of_germ,
    ← nativeTensorGerm_smul A P Q x U a (p ⊗ₜ q)]
  apply congrArg (nativeTensorGerm A P Q x U)
  let a' : (ADiag A x).obj U := a
  exact (TensorProduct.smul_tmul' a' p q).symm

private theorem backwardSet_smul_right_native (r : A.stalk x)
    (m : PStalk A P x) (n : PStalk A Q x) :
    backwardSetNative A P Q x m (r • n) = r • backwardSetNative A P Q x m n := by
  obtain ⟨U, a, p, q, hr, hm, hn⟩ :=
    PresheafOfModules.ModuleColimit.jointly_surjective₃'
      (hcR := hcA A x) (hcM := hcP A P x) (hcM' := hcQ A Q x) r m n
  have hr' : nativeRingGerm A x U a = r := hr
  have hm' : nativeModuleGerm A x P U p = m := hm
  have hn' : nativeModuleGerm A x Q U q = n := hn
  rw [← hr', ← hm', ← hn',
    ← nativeModuleGerm_smul A x Q U a q,
    backwardSetNative_of_germ, backwardSetNative_of_germ,
    ← nativeTensorGerm_smul A P Q x U a (p ⊗ₜ q)]
  congr 1
  let a' : (ADiag A x).obj U := a
  change p ⊗ₜ[(ADiag A x).obj U] (a' • q) = a' • (p ⊗ₜ[(ADiag A x).obj U] q)
  exact TensorProduct.tmul_smul a' p q

private noncomputable def backwardNative :
    NativeTensor A P Q x →ₗ[A.stalk x] PStalk A (P ⊗ Q) x :=
  TensorProduct.lift <| LinearMap.mk₂ (A.stalk x) (backwardSetNative A P Q x)
    (backwardSetNative_add_left A P Q x) (backwardSet_smul_left_native A P Q x)
    (backwardSetNative_add_right A P Q x) (backwardSet_smul_right_native A P Q x)

private theorem backwardNative_tmul (m : PStalk A P x) (n : PStalk A Q x) :
    backwardNative A P Q x (m ⊗ₜ[A.stalk x] n) = backwardSetNative A P Q x m n := rfl

private theorem forwardNative_backwardNative (z : NativeTensor A P Q x) :
    forwardNative A P Q x (backwardNative A P Q x z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
      obtain ⟨U, p, q, hp, hq⟩ :=
        PresheafOfModules.ModuleColimit.ιM_jointly_surjective₂
          (hcR := hcA A x) (hcM := hcP A P x) (hcM' := hcQ A Q x) m n
      have hp' : nativeModuleGerm A x P U p = m := hp
      have hq' : nativeModuleGerm A x Q U q = n := hq
      rw [← hp', ← hq', backwardNative_tmul, backwardSetNative_of_germ]
      exact forwardNativeAdd_tmul A P Q x U p q
  | add z w hz hw =>
      rw [map_add, map_add, hz, hw]

private theorem backwardNative_forwardNative (z : PStalk A (P ⊗ Q) x) :
    backwardNative A P Q x (forwardNative A P Q x z) = z := by
  obtain ⟨U, t, ht⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
    (hcR := hcA A x) (hcM := hcT A P Q x) z
  have ht' : nativeTensorGerm A P Q x U t = z := ht
  rw [← ht']
  clear z ht ht'
  induction t using TensorProduct.inductionOn with
  | tmul p q =>
      rw [show forwardNative A P Q x
          (nativeTensorGerm A P Q x U (p ⊗ₜ q)) =
          _ from forwardNativeAdd_tmul A P Q x U p q,
        backwardNative_tmul, backwardSetNative_of_germ]
  | add s t hs ht =>
      let s' : (TDiag A P Q x).obj U := s
      let t' : (TDiag A P Q x).obj U := t
      change backwardNative A P Q x
          (forwardNative A P Q x
            (nativeTensorGerm A P Q x U (s' + t'))) =
        nativeTensorGerm A P Q x U (s' + t')
      rw [nativeTensorGerm_add, map_add, map_add, hs, ht]

/-- Canonical tensor product comparison for stalks of modules over a commutative-ring
presheaf. No sheaf condition on the modules or assumption on the space is required. -/
noncomputable def stalkTensorEquiv :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (P ⊗ Q).presheaf x ≃ₗ[A.stalk x]
      TensorProduct (A.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Q.presheaf x) where
  toFun := forwardNative A P Q x
  invFun := backwardNative A P Q x
  left_inv := backwardNative_forwardNative A P Q x
  right_inv := forwardNative_backwardNative A P Q x
  map_add' := map_add (forwardNative A P Q x)
  map_smul' := map_smul (forwardNative A P Q x)

/-- A pure tensor section at a common neighborhood maps to the tensor of germs. -/
theorem stalkTensorEquiv_germ_tmul (V : Opens X) (hx : x ∈ V)
    (p : P.obj (op V)) (q : Q.obj (op V)) :
    stalkTensorEquiv A P Q x
        (TopCat.Presheaf.germ (P ⊗ Q).presheaf V x hx
          (show (P ⊗ Q).obj (op V) from p ⊗ₜ q)) =
      TopCat.Presheaf.germ P.presheaf V x hx p ⊗ₜ[A.stalk x]
        TopCat.Presheaf.germ Q.presheaf V x hx q := by
  let U : OpenNhds x := ⟨V, hx⟩
  change forwardNativeAdd A P Q x
      (nativeTensorGerm A P Q x (op U)
        (show (PDiag A (P ⊗ Q) x).obj (op U) from p ⊗ₜ q)) =
    nativeModuleGerm A x P (op U) p ⊗ₜ[A.stalk x]
      nativeModuleGerm A x Q (op U) q
  exact forwardNativeAdd_tmul A P Q x (op U) p q


private noncomputable local instance nativeStalkModule
    (L : PresheafOfModulesOfCommRing.{u} A) :
    Module (A.stalk x) (PresheafOfModulesOfCommRing.PStalk A L x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier L x

private noncomputable def stalkMapAdd (f : P ⟶ Q) :
    PresheafOfModulesOfCommRing.PStalk A P x →+ PresheafOfModulesOfCommRing.PStalk A Q x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf (A ⋙ forget₂ CommRingCat RingCat)).map f)).hom

private theorem stalkMapAdd_germ (f : P ⟶ Q) (U : TopologicalSpace.Opens X) (hx : x ∈ U)
    (p : P.obj (op U)) :
    stalkMapAdd A P Q x f (TopCat.Presheaf.germ P.presheaf U x hx p) =
      TopCat.Presheaf.germ Q.presheaf U x hx (f.app (op U) p) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf (A ⋙ forget₂ CommRingCat RingCat)).map f) p

/-- The map on native module stalks, linear over the unchanged ring stalk. -/
noncomputable def stalkMapLinear (f : P ⟶ Q) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf x →ₗ[A.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Q.presheaf x where
  toFun := stalkMapAdd A P Q x f
  map_add' := map_add (stalkMapAdd A P Q x f)
  map_smul' r m := by
    obtain ⟨U, a, p, hr, hm⟩ :=
      PresheafOfModules.ModuleColimit.jointly_surjective₂
        (hcR := PresheafOfModulesOfCommRing.hcA A x)
        (hcM := PresheafOfModulesOfCommRing.hcP A P x) r m
    let V : TopologicalSpace.Opens X := U.unop.1
    have hxV : x ∈ V := U.unop.2
    let a' : A.obj (op V) := a
    let p' : P.obj (op V) := p
    rw [← hr, ← hm]
    change stalkMapAdd A P Q x f
        (TopCat.Presheaf.germ A V x hxV a' •
          TopCat.Presheaf.germ P.presheaf V x hxV p') =
      TopCat.Presheaf.germ A V x hxV a' •
        stalkMapAdd A P Q x f
          (TopCat.Presheaf.germ P.presheaf V x hxV p')
    rw [← PresheafOfModules.germ_smul P]
    rw [stalkMapAdd_germ, stalkMapAdd_germ]
    rw [show f.app (op V) (a' • p') = a' • f.app (op V) p' from
      (f.app (op V)).hom.map_smul a' p']
    exact PresheafOfModules.germ_smul Q x V hxV a' (f.app (op V) p')

/-- The underlying additive map of the linear stalk map. -/
theorem stalkMapLinear_apply_stalkFunctor (f : P ⟶ Q)
    (z : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P.presheaf x) :
    stalkMapLinear A P Q x f z =
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf (A ⋙ forget₂ CommRingCat RingCat)).map f)).hom z := by
  rfl

/-- A stalk map acts on a germ by applying the presheaf morphism to its section. -/
theorem stalkMapLinear_germ (f : P ⟶ Q) (U : TopologicalSpace.Opens X) (hx : x ∈ U)
    (p : P.obj (op U)) :
    stalkMapLinear A P Q x f (TopCat.Presheaf.germ P.presheaf U x hx p) =
      TopCat.Presheaf.germ Q.presheaf U x hx (f.app (op U) p) := by
  exact stalkMapAdd_germ A P Q x f U hx p



variable {X : TopCat.{u}} (A : X.Presheaf CommRingCat.{u})
  (P Q : PresheafOfModulesOfCommRing.{u} A) (x : X)

/-- The stalk tensor comparison is natural in both module arguments. -/
theorem stalkTensorEquiv_naturality
    {P' Q' : PresheafOfModulesOfCommRing.{u} A} (f : P ⟶ P') (g : Q ⟶ Q')
    (z : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (P ⊗ Q).presheaf x) :
    PresheafOfModulesOfCommRing.stalkTensorEquiv A P' Q' x
        (PresheafOfModulesOfCommRing.stalkMapLinear A (P ⊗ Q) (P' ⊗ Q') x
          (f ⊗ₘ g) z) =
      TensorProduct.map
        (PresheafOfModulesOfCommRing.stalkMapLinear A P P' x f)
        (PresheafOfModulesOfCommRing.stalkMapLinear A Q Q' x g)
        (PresheafOfModulesOfCommRing.stalkTensorEquiv A P Q x z) := by
  obtain ⟨U, hxU, t, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (P ⊗ Q).presheaf z
  induction t using TensorProduct.inductionOn with
  | tmul p q =>
      let pq : (P ⊗ Q).obj (op U) := p ⊗ₜ[A.obj (op U)] q
      let p'q' : (P' ⊗ Q').obj (op U) :=
        f.app (op U) p ⊗ₜ[A.obj (op U)] g.app (op U) q
      have hpqmap : (f ⊗ₘ g).app (op U) pq = p'q' := by
        dsimp [pq, p'q']
        change ((f.app' (op U)) ⊗ₘ (g.app' (op U))).hom
            (p ⊗ₜ[A.obj (op U)] q) = _
        exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _
      change PresheafOfModulesOfCommRing.stalkTensorEquiv A P' Q' x
          (PresheafOfModulesOfCommRing.stalkMapLinear A (P ⊗ Q) (P' ⊗ Q') x
            (f ⊗ₘ g)
            (TopCat.Presheaf.germ (P ⊗ Q).presheaf U x hxU pq)) =
        TensorProduct.map
          (PresheafOfModulesOfCommRing.stalkMapLinear A P P' x f)
          (PresheafOfModulesOfCommRing.stalkMapLinear A Q Q' x g)
          (PresheafOfModulesOfCommRing.stalkTensorEquiv A P Q x
            (TopCat.Presheaf.germ (P ⊗ Q).presheaf U x hxU pq))
      rw [PresheafOfModulesOfCommRing.stalkMapLinear_germ, hpqmap]
      calc
        _ = TopCat.Presheaf.germ P'.presheaf U x hxU (f.app (op U) p) ⊗ₜ[A.stalk x]
              TopCat.Presheaf.germ Q'.presheaf U x hxU (g.app (op U) q) := by
          exact PresheafOfModulesOfCommRing.stalkTensorEquiv_germ_tmul
            A P' Q' x U hxU (f.app (op U) p) (g.app (op U) q)
        _ = TensorProduct.map
              (PresheafOfModulesOfCommRing.stalkMapLinear A P P' x f)
              (PresheafOfModulesOfCommRing.stalkMapLinear A Q Q' x g)
              (TopCat.Presheaf.germ P.presheaf U x hxU p ⊗ₜ[A.stalk x]
                TopCat.Presheaf.germ Q.presheaf U x hxU q) := by
          rw [TensorProduct.map_tmul,
            PresheafOfModulesOfCommRing.stalkMapLinear_germ,
            PresheafOfModulesOfCommRing.stalkMapLinear_germ]
        _ = _ := by
          congr 1
          exact (PresheafOfModulesOfCommRing.stalkTensorEquiv_germ_tmul
            A P Q x U hxU p q).symm
  | add s t hs ht =>
      let germ := (TopCat.Presheaf.germ (P ⊗ Q).presheaf U x hxU).hom
      let L : (P ⊗ Q).obj (op U) →+
          PresheafOfModulesOfCommRing.NativeTensor A P' Q' x :=
        (PresheafOfModulesOfCommRing.stalkTensorEquiv A P' Q' x).toLinearMap.toAddMonoidHom.comp
          ((PresheafOfModulesOfCommRing.stalkMapLinear A (P ⊗ Q) (P' ⊗ Q') x
            (f ⊗ₘ g)).toAddMonoidHom.comp germ)
      let R : (P ⊗ Q).obj (op U) →+
          PresheafOfModulesOfCommRing.NativeTensor A P' Q' x :=
        (TensorProduct.map
          (PresheafOfModulesOfCommRing.stalkMapLinear A P P' x f)
          (PresheafOfModulesOfCommRing.stalkMapLinear A Q Q' x g)).toAddMonoidHom.comp
            ((PresheafOfModulesOfCommRing.stalkTensorEquiv A P Q x).toLinearMap.toAddMonoidHom.comp
              germ)
      have hs' : L s = R s := hs
      have ht' : L t = R t := ht
      change L (s + t) = R (s + t)
      calc
        _ = L s + L t := map_add L s t
        _ = R s + R t := congrArg₂ (fun a b ↦ a + b) hs' ht'
        _ = _ := (map_add R s t).symm


end PresheafOfModulesOfCommRing
