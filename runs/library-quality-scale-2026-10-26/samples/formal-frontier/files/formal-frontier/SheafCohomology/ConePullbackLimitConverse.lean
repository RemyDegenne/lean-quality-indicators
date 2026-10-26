/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original expression and destination adaptation: Formal Frontier Agents.
-/

module
public import SheafCohomology.ConePullbackLimit

public section

/-!
# Fixed-base converse for limits of sheafed spaces

Over a limiting cone of underlying spaces, a limiting native cone makes its
actual inverse-image sheaf cocone colimiting. Together with the forward
criterion this gives an equivalence of the two universal properties.
-/

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u vj wj

namespace AlgebraicGeometry.SheafedSpace

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
variable {J : Type wj} [Category.{vj} J]

private theorem triangleMap_id_first {X Y : TopCat.{w}} (p : X ⟶ Y)
    {F : Y.Sheaf A} {G : X.Sheaf A}
    (a : (TopCat.Sheaf.pullback A p).obj F ⟶ G) :
    triangleMap A (Category.id_comp p) a ≫ TopCat.Sheaf.pullbackIdHom A X G = a := by
  change triangleMap A (rfl : (𝟙 X) ≫ p = p) a ≫
    TopCat.Sheaf.pullbackIdHom A X G = a
  simp only [triangleMap, TopCat.Sheaf.pullbackCompInv,
    TopCat.Sheaf.pullbackCompIso_comp_id, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.comp_obj]
  simp only [Category.id_comp]
  change (TopCat.Sheaf.pullbackIdInv A X ((TopCat.Sheaf.pullback A p).obj F) ≫
      (TopCat.Sheaf.pullback A (𝟙 X)).map a) ≫
      TopCat.Sheaf.pullbackIdHom A X G = a
  rw [Category.assoc, TopCat.Sheaf.pullbackIdHom_naturality]
  simp only [← Category.assoc, TopCat.Sheaf.pullbackIdInv,
    TopCat.Sheaf.pullbackIdHom, Iso.inv_hom_id_app,
    Functor.id_obj, Category.id_comp]

/-- A native limit over a limiting space cone forces the canonical cocone
of inverse-image sheaves to be colimiting. -/
noncomputable def isColimit_conePullbackCocone_of_isLimit
    (S : Jᵒᵖ ⥤ SheafedSpace A) (C : Cone S)
    (hbase : IsLimit ((forget A).mapCone C)) (hC : IsLimit C) :
    IsColimit (conePullbackCocone A S C) := by
  apply IsColimit.ofExistsUnique
  intro K
  let Q := coneOfPullbackCocone A S ((forget A).mapCone C) K
  let m : Q.pt ⟶ C.pt := hC.lift Q
  have hm : m = hC.lift Q := rfl
  have hfac (i : Jᵒᵖ) : m ≫ C.π.app i = Q.π.app i := hC.fac Q i
  have hbase_m : m.hom.base = 𝟙 (C.pt : TopCat) := by
    apply hbase.hom_ext
    intro i
    have heq := congrArg (fun arrow : Q.pt ⟶ S.obj i ↦ arrow.hom.base) (hfac i)
    change m.hom.base ≫ ((forget A).mapCone C).π.app i =
      ((coneOfPullbackCocone A S ((forget A).mapCone C) K).π.app i).hom.base at heq
    rw [coneOfPullbackCocone_π_base] at heq
    exact heq.trans (Category.id_comp _).symm
  rcases m with ⟨⟨mbase, mc⟩⟩
  change mbase = 𝟙 _ at hbase_m
  subst mbase
  let native : Q.pt ⟶ C.pt := ⟨⟨𝟙 _, mc⟩⟩
  have hnorm (i : Jᵒᵖ) :
      triangleMap A (Category.id_comp ((C.π.app i).hom.base))
          (sheafMate A (C.π.app i)) =
        sheafMate A (C.π.app i) ≫
          TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf := by
    calc
      _ = triangleMap A (Category.id_comp ((C.π.app i).hom.base))
            (sheafMate A (C.π.app i)) ≫
            (TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫
              TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf) := by
              simp only [TopCat.Sheaf.pullbackIdHom, TopCat.Sheaf.pullbackIdInv,
                Iso.hom_inv_id_app]
              exact (Category.comp_id _).symm
      _ = (triangleMap A (Category.id_comp ((C.π.app i).hom.base))
            (sheafMate A (C.π.app i)) ≫
              TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf) ≫
              TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf := by
              rw [Category.assoc]
      _ = _ := congrArg (· ≫ TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf)
        (triangleMap_id_first A (C.π.app i).hom.base (sheafMate A (C.π.app i)))
  refine ⟨TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf ≫
    sheafMate A native, ?_, ?_⟩
  · intro i
    have htriangle := sheafMate_triangle A (Q.π.app (op i)) native
      (C.π.app (op i)) (hfac (op i))
    rw [coneOfPullbackCocone_π_mate] at htriangle
    change triangleMap A (Category.id_comp ((C.π.app (op i)).hom.base))
      (sheafMate A (C.π.app (op i))) ≫ sheafMate A native = K.ι.app i at htriangle
    rw [hnorm] at htriangle
    change sheafMate A (C.π.app (op i)) ≫
      (TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf ≫
        sheafMate A native) = K.ι.app i
    exact (Category.assoc _ _ _).symm.trans htriangle
  · intro d hd
    let t : Q.pt ⟶ C.pt := InducedCategory.homMk {
      base := 𝟙 (C.pt : TopCat)
      c := (((TopCat.Sheaf.pullbackPushforwardAdjunction A (𝟙 (C.pt : TopCat))).homEquiv
        C.pt.sheaf K.pt)
        (TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫ d)).hom }
    have htMate : sheafMate A t =
        TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫ d := by
      unfold t sheafMate
      exact Equiv.symm_apply_apply _ _
    have htFac (i : Jᵒᵖ) : t ≫ C.π.app i = Q.π.app i := by
      apply sheafMate_triangle_converse A (Q.π.app i) t (C.π.app i)
        (Category.id_comp _)
      change triangleMap A (Category.id_comp ((C.π.app i).hom.base))
        (sheafMate A (C.π.app i)) ≫ sheafMate A t = sheafMate A (Q.π.app i)
      rw [hnorm, htMate]
      have hleg := hd (unop i)
      change sheafMate A (C.π.app i) ≫ d = K.ι.app (unop i) at hleg
      have hstage : sheafMate A (C.π.app i) ≫ d = sheafMate A (Q.π.app i) :=
        hleg.trans (coneOfPullbackCocone_π_mate A S ((forget A).mapCone C) K i).symm
      calc
        (sheafMate A (C.π.app i) ≫
              TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf) ≫
            (TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫ d) =
          sheafMate A (C.π.app i) ≫
            ((TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf ≫
              TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf) ≫ d) := by
                simp only [Category.assoc]
        _ = sheafMate A (C.π.app i) ≫ d := by
          rw [show TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf ≫
            TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf =
              𝟙 C.pt.sheaf from Iso.inv_hom_id_app (TopCat.Sheaf.pullbackIdIso A (C.pt : TopCat)) _]
          simp
        _ = sheafMate A (Q.π.app i) := hstage
    have htEq : t = native := (hC.uniq Q t htFac).trans hm.symm
    have hcongr {f g : Q.pt ⟶ C.pt} (h : f = g) :
        sheafMate A f ≍ sheafMate A g := by
      cases h
      rfl
    have hmMate : sheafMate A native =
        TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫ d := by
      exact (eq_of_heq (hcongr (f := t) (g := native) htEq)).symm.trans htMate
    have hcancel : TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫
        d = TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf ≫
          (TopCat.Sheaf.pullbackIdInv A (C.pt : TopCat) C.pt.sheaf ≫
            sheafMate A native) := by
      rw [← hmMate]
      simp only [TopCat.Sheaf.pullbackIdHom, TopCat.Sheaf.pullbackIdInv,
        Iso.hom_inv_id_app_assoc]
    exact (cancel_epi (TopCat.Sheaf.pullbackIdHom A (C.pt : TopCat) C.pt.sheaf)).mp hcancel

/-- With the actual base cone limiting, the native limit property is equivalent
to the sheaf-cocone colimit property; no existence of sheaf colimits is required. -/
theorem nonempty_isLimit_iff_isColimit_conePullbackCocone
    (S : Jᵒᵖ ⥤ SheafedSpace A) (C : Cone S)
    (hbase : IsLimit ((forget A).mapCone C)) :
    Nonempty (IsLimit C) ↔ Nonempty (IsColimit (conePullbackCocone A S C)) := by
  constructor
  · rintro ⟨hC⟩
    exact ⟨isColimit_conePullbackCocone_of_isLimit A S C hbase hC⟩
  · rintro ⟨hK⟩
    exact ⟨isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone
      A S C hbase hK⟩

end AlgebraicGeometry.SheafedSpace
