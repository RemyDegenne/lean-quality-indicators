public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ConcreteCategory Opposite

open TopologicalSpace

universe u v

namespace SheafCohomology.CompactOpenSections

variable {X : Type u} [TopologicalSpace X]

variable {C : Type (v + 1)} [Category.{v} C]

variable {FC : C → C → Type*} {CC : C → Type v}

variable [∀ A B, FunLike (FC A B) (CC A) (CC B)]

variable [instCC : ConcreteCategory C FC] [HasColimitsOfSize.{v, v} C]

variable [HasLimitsOfSize.{u, u} C]

variable [PreservesFilteredColimits (forget C)]

variable [PreservesLimitsOfSize.{u, u} (forget C)]

variable [instReflectsIsomorphisms : (forget C).ReflectsIsomorphisms]

local notation "sections" => sectionsOf

variable [UnivLE.{u, v}]

variable [HasWeakSheafify
  (Opens.grothendieckTopology X) C]

variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  C]

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) C)

omit [UnivLE.{u, v}] in
theorem explicitSectionsComparison_surjective
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Surjective (explicitSectionsComparison F U) := by
  classical
  intro s
  choose V f hxV hVcompact c hc using fun x : U =>
    exists_compact_open_local_preimage F U s x.1 x.2
  have hcover : (U : Set X) ⊆ ⋃ x : U, (V x : Set X) := by
    intro x hxU
    exact Set.mem_iUnion.mpr ⟨⟨x, hxU⟩, hxV ⟨x, hxU⟩⟩
  obtain ⟨S, hS⟩ := hU.elim_finite_subcover
    (fun x : U => (V x : Set X)) (fun x => (V x).2) hcover
  have hrep : ∀ x : U,
      ∃ (i : I) (a : ToType ((F.obj i).obj.obj (op (V x)))),
        colimit.ι (F ⋙ sections (V x)) i a = c x := by
    intro x
    exact Concrete.colimit_exists_rep (F ⋙ sections (V x)) (c x)
  choose i a ha using hrep
  let i₀ : I := Classical.choice IsFiltered.nonempty
  let O : Finset I := insert i₀ (S.image i)
  have hiO (x : U) (hxS : x ∈ S) : i x ∈ O := by
    simp only [O, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨x, hxS, rfl⟩
  let H : Finset (Σ' (A B : I) (_ : A ∈ O) (_ : B ∈ O), A ⟶ B) := ∅
  let k : I := IsFiltered.sup O H
  let p (x : {x // x ∈ S}) : i x.1 ⟶ k :=
    IsFiltered.toSup O H (hiO x.1 x.2)
  let b (x : {x // x ∈ S}) :
      ToType ((F.obj k).obj.obj (op (V x.1))) :=
    (F ⋙ sections (V x.1)).map (p x) (a x.1)
  have hbcolim (x : {x // x ∈ S}) :
      colimit.ι (F ⋙ sections (V x.1)) k (b x) = c x.1 := by
    calc
      _ = colimit.ι (F ⋙ sections (V x.1)) (i x.1) (a x.1) := by
        simpa only [b, ConcreteCategory.comp_apply] using
          congr_hom (colimit.w (F ⋙ sections (V x.1)) (p x)) (a x.1)
      _ = _ := ha x.1
  have hbtarget (x : {x // x ∈ S}) :
      explicitSectionsComparison F (V x.1)
          (colimit.ι (F ⋙ sections (V x.1)) k (b x)) =
        (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map (f x.1).op s := by
    rw [hbcolim]
    exact hc x.1
  let W : {x // x ∈ S} → Opens X := fun x => V x.1
  have heventual (x y : {x // x ∈ S}) :
      ∃ (m : I) (q : k ⟶ m),
        (F ⋙ sections (V x.1 ⊓ V y.1)).map q
            ((F.obj k).obj.map
              (homOfLE inf_le_left : (V x.1 ⊓ V y.1) ⟶ V x.1).op (b x)) =
          (F ⋙ sections (V x.1 ⊓ V y.1)).map q
            ((F.obj k).obj.map
              (homOfLE inf_le_right : (V x.1 ⊓ V y.1) ⟶ V y.1).op (b y)) := by
    apply ((colimit.isColimit (F ⋙ sections (W x ⊓ W y))).eq_iff' _ _).mp
    have hI : IsCompact ((W x ⊓ W y : Opens X) : Set X) :=
      (hVcompact x.1).inter_of_isOpen
        (hVcompact y.1) (V x.1).2 (V y.1).2
    apply explicitSectionsComparison_injective F (W x ⊓ W y) hI
    calc
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op
          (explicitSectionsComparison F (W x)
            (colimit.ι (F ⋙ sections (W x)) k (b x))) :=
        explicitSectionsComparison_ι_naturality F
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x) k (b x)
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op
          ((sheafify (Opens.grothendieckTopology X)
            (underlyingPresheafColimit F)).map (f x.1).op s) := by
              exact _root_.congr_arg
                ((sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map
                    (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op)
                (hbtarget x)
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op
          ((sheafify (Opens.grothendieckTopology X)
            (underlyingPresheafColimit F)).map (f y.1).op s) := by
              rw [← ConcreteCategory.comp_apply,
                ← ConcreteCategory.comp_apply,
                ← (sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map_comp,
                ← (sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map_comp]
              rfl
      _ = (sheafify (Opens.grothendieckTopology X)
          (underlyingPresheafColimit F)).map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op
          (explicitSectionsComparison F (W y)
            (colimit.ι (F ⋙ sections (W y)) k (b y))) := by
              exact _root_.congr_arg
                ((sheafify (Opens.grothendieckTopology X)
                  (underlyingPresheafColimit F)).map
                    (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op)
                (hbtarget y).symm
      _ = _ := (explicitSectionsComparison_ι_naturality F
        (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y) k (b y)).symm
  let Pairs : Finset ({x // x ∈ S} × {x // x ∈ S}) := Finset.univ
  choose m q hq using fun z : {x // x ∈ S} × {x // x ∈ S} =>
    heventual z.1 z.2
  let O' : Finset I := insert k (Pairs.image m)
  have hkO' : k ∈ O' := by simp [O']
  have hmO' (z : {x // x ∈ S} × {x // x ∈ S}) : m z ∈ O' := by
    simp only [O', Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨z, Finset.mem_univ z, rfl⟩
  let H' : Finset (Σ' (A B : I) (_ : A ∈ O') (_ : B ∈ O'), A ⟶ B) :=
    Pairs.attach.image fun z => ⟨k, m z.1, hkO', hmO' z.1, q z.1⟩
  let l : I := IsFiltered.sup O' H'
  let p' : k ⟶ l := IsFiltered.toSup O' H' hkO'
  let r (z : {x // x ∈ S} × {x // x ∈ S}) : m z ⟶ l :=
    IsFiltered.toSup O' H' (hmO' z)
  have hp' (z : {x // x ∈ S} × {x // x ∈ S}) :
      q z ≫ r z = p' := by
    apply IsFiltered.toSup_commutes O' H' hkO' (hmO' z)
    simp only [H', Finset.mem_image]
    exact ⟨⟨z, Finset.mem_univ z⟩,
      Finset.mem_attach Pairs ⟨z, Finset.mem_univ z⟩, rfl⟩
  let sf : ∀ x, ToType ((F.obj l).obj.obj (op (W x))) := fun x =>
    (F.map p').hom.app (op (W x)) (b x)
  have hcompat : ∀ x y,
      (F.obj l).obj.map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (sf x) =
        (F.obj l).obj.map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (sf y) := by
    intro x y
    let z : {x // x ∈ S} × {x // x ∈ S} := ⟨x, y⟩
    calc
      (F.obj l).obj.map
          (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (sf x) =
        (F.map p').hom.app (op (W x ⊓ W y))
          ((F.obj k).obj.map
            (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (b x)) := by
            simpa only [sf, ConcreteCategory.comp_apply] using
              (congr_hom ((F.map p').hom.naturality
                (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op) (b x)).symm
      _ = (F.map (r z)).hom.app (op (W x ⊓ W y))
          ((F.map (q z)).hom.app (op (W x ⊓ W y))
            ((F.obj k).obj.map
              (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (b x))) := by
            rw [← hp' z, F.map_comp]
            change (((F.map (q z)).hom.app (op (W x ⊓ W y)) ≫
              (F.map (r z)).hom.app (op (W x ⊓ W y)))
                ((F.obj k).obj.map
                  (homOfLE inf_le_left : (W x ⊓ W y) ⟶ W x).op (b x))) = _
            rw [ConcreteCategory.comp_apply]
      _ = (F.map (r z)).hom.app (op (W x ⊓ W y))
          ((F.map (q z)).hom.app (op (W x ⊓ W y))
            ((F.obj k).obj.map
              (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (b y))) := by
            exact _root_.congr_arg
              ((F.map (r z)).hom.app (op (W x ⊓ W y))) (hq z)
      _ = (F.map p').hom.app (op (W x ⊓ W y))
          ((F.obj k).obj.map
            (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (b y)) := by
            rw [← hp' z, F.map_comp]
            change _ = (((F.map (q z)).hom.app (op (W x ⊓ W y)) ≫
              (F.map (r z)).hom.app (op (W x ⊓ W y)))
                ((F.obj k).obj.map
                  (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (b y)))
            rw [ConcreteCategory.comp_apply]
      _ = (F.obj l).obj.map
          (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op (sf y) := by
            simpa only [sf, ConcreteCategory.comp_apply] using
              congr_hom ((F.map p').hom.naturality
                (homOfLE inf_le_right : (W x ⊓ W y) ⟶ W y).op) (b y)
  have hcoverOpen : U ≤ ⨆ x : {x // x ∈ S}, W x := by
    intro x hxU
    rw [Opens.mem_iSup]
    obtain ⟨y, hyS, hxy⟩ := Set.mem_iUnion₂.mp (hS hxU)
    exact ⟨⟨y, hyS⟩, hxy⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (X := TopCat.of X) (F.obj l) W U
    (fun x => f x.1) hcoverOpen sf hcompat
  refine ⟨colimit.ι (F ⋙ sections U) l g, ?_⟩
  let aP := (presheafToSheaf (Opens.grothendieckTopology X)
    C).obj (underlyingPresheafColimit F)
  apply TopCat.Sheaf.eq_of_locally_eq'
    (X := TopCat.of X) aP W U (fun x => f x.1) hcoverOpen
  intro y
  calc
    (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).map (f y.1).op
        (explicitSectionsComparison F U
          (colimit.ι (F ⋙ sections U) l g)) =
      explicitSectionsComparison F (W y)
        (colimit.ι (F ⋙ sections (W y)) l
          ((F.obj l).obj.map (f y.1).op g)) := by
            exact (explicitSectionsComparison_ι_naturality F
              (f y.1) l g).symm
    _ = explicitSectionsComparison F (W y)
        (colimit.ι (F ⋙ sections (W y)) l (sf y)) := by rw [hg y]
    _ = explicitSectionsComparison F (W y)
        (colimit.ι (F ⋙ sections (W y)) k (b y)) := by
          apply _root_.congr_arg (explicitSectionsComparison F (W y))
          change colimit.ι (F ⋙ sections (W y)) l
              ((F ⋙ sections (W y)).map p' (b y)) = _
          rw [← ConcreteCategory.comp_apply]
          exact congr_hom (colimit.w (F ⋙ sections (W y)) p') (b y)
    _ = (sheafify (Opens.grothendieckTopology X)
        (underlyingPresheafColimit F)).map (f y.1).op s := hbtarget y

end SheafCohomology.CompactOpenSections
end
end
