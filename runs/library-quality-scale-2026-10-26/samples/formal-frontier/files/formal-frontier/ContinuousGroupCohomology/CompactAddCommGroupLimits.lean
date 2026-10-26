/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import ContinuousGroupCohomology.CompactAddCommGroup
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.CofilteredSystem

public section

/-!
# Limits of compact Hausdorff additive commutative groups

This file constructs limits in `CompHausAddCommGrp`. The limit is the closed
subspace of compatible tuples in the product of the underlying compact
Hausdorff spaces, with pointwise addition. The forgetful functor to `CompHaus`
preserves this explicit limit. For cofiltered diagrams, it also identifies the
range of each projection, proves that a pointwise-surjective natural
transformation induces a surjection on limits, and proves that pointwise exact
natural transformations induce exact maps on limits.

No total-disconnectedness or scalar topology is imposed.
-/

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Set CategoryTheory.FunctorToTypes

noncomputable section

universe u v

namespace CompHausAddCommGrp

variable {J : Type v} [SmallCategory J]
variable (F : J ⥤ CompHausAddCommGrp.{max u v})

/-- The compatible tuples underlying a limit of compact Hausdorff additive
commutative groups. -/
@[expose] def limitConePtAux : AddSubgroup (∀ j : J, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f (x i) = x j}
  zero_mem' := by simp
  add_mem' hx hy _ _ f := by simp [hx f, hy f]
  neg_mem' hx _ _ f := by simp [hx f]

instance : AddCommGroup
    (CompHaus.limitCone (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).pt :=
  inferInstanceAs (AddCommGroup (limitConePtAux F))

instance : IsTopologicalAddGroup
    (CompHaus.limitCone (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).pt :=
  inferInstanceAs (IsTopologicalAddGroup (limitConePtAux F))

/-- The explicit limit cone in compact Hausdorff additive commutative groups. -/
abbrev limitCone : Cone F where
  pt :=
    { toCompHaus :=
        (CompHaus.limitCone (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).pt
      addCommGroup := inferInstance
      isTopologicalAddGroup := inferInstance }
  π :=
    { app := fun j => ConcreteCategory.ofHom
        { toFun := fun x => x.1 j
          map_zero' := rfl
          map_add' := fun _ _ => rfl
          continuous_toFun :=
            ((CompHaus.limitCone
              (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).π.app j).hom.hom.continuous }
      naturality := fun i j f => by
        apply hom_ext
        ext x
        exact (x.2 f).symm }

/-- The explicit cone is limiting. -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift S := ConcreteCategory.ofHom
    { toFun :=
        (CompHaus.limitConeIsLimit
          (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).lift
            ((forget₂ CompHausAddCommGrp CompHaus).mapCone S)
      map_zero' := Subtype.ext (funext fun j => (S.π.app j).hom.map_zero)
      map_add' := fun x y =>
        Subtype.ext (funext fun j => (S.π.app j).hom.map_add x y)
      continuous_toFun :=
        ((CompHaus.limitConeIsLimit
          (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).lift
            ((forget₂ CompHausAddCommGrp CompHaus).mapCone S)).hom.hom.continuous }
  uniq S m h := by
    apply (forget₂ CompHausAddCommGrp CompHaus).map_injective
    exact
      (CompHaus.limitConeIsLimit
        (F ⋙ forget₂ CompHausAddCommGrp CompHaus)).uniq
          ((forget₂ CompHausAddCommGrp CompHaus).mapCone S)
          ((forget₂ CompHausAddCommGrp CompHaus).map m)
          (fun j => congrArg (forget₂ CompHausAddCommGrp CompHaus).map (h j))

instance : HasLimit F where
  exists_limit := ⟨⟨limitCone F, limitConeIsLimit F⟩⟩

instance : PreservesLimit F (forget₂ CompHausAddCommGrp CompHaus) :=
  preservesLimit_of_preserves_limit_cone
    (limitConeIsLimit F)
    (CompHaus.limitConeIsLimit (F ⋙ forget₂ CompHausAddCommGrp CompHaus))

private abbrev FiniteDiagramArrow (G : Finset J) :=
  Σ' (X Y : J) (_ : X ∈ G) (_ : Y ∈ G), X ⟶ Y

private structure PointedFiniteDiagram (j : J) where
  objects : Finset J
  point_mem : j ∈ objects
  arrows : Finset (FiniteDiagramArrow objects)

private def partialSectionsAt (j : J) (x : F.obj j)
    (D : PointedFiniteDiagram j) : Set (∀ k, F.obj k) :=
  {s | s j = x ∧ ∀ {f : FiniteDiagramArrow D.objects} (_ : f ∈ D.arrows),
    F.map f.2.2.2.2 (s f.1) = s f.2.1}

private theorem partialSectionsAt_nonempty [IsCofilteredOrEmpty J]
    (j : J) (x : F.obj j)
    (hx : x ∈ (F ⋙ forget CompHausAddCommGrp).eventualRange j)
    (D : PointedFiniteDiagram j) : (partialSectionsAt F j x D).Nonempty := by
  classical
  let _ : Nonempty J := ⟨j⟩
  let _ : IsCofiltered J := ⟨⟩
  obtain ⟨y, hy⟩ :=
    ((F ⋙ forget CompHausAddCommGrp).mem_eventualRange_iff.1 hx)
      (IsCofiltered.infTo D.objects D.arrows D.point_mem)
  refine ⟨fun k => if hk : k ∈ D.objects then
      F.map (IsCofiltered.infTo D.objects D.arrows hk) y else 0, ?_⟩
  constructor
  · simpa [D.point_mem] using hy
  · rintro ⟨X, Y, hX, hY, f⟩ hf
    dsimp only
    rwa [dite_eq_left hX, dite_eq_left hY, ← comp_apply, ← F.map_comp,
      @IsCofiltered.infTo_commutes _ _ _ D.objects D.arrows]

private theorem partialSectionsAt_directed (j : J) (x : F.obj j) :
    Directed GE.ge (partialSectionsAt F j x) := by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.objects →
      FiniteDiagramArrow (A.objects ⊔ B.objects) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1,
      Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.objects →
      FiniteDiagramArrow (A.objects ⊔ B.objects) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1,
      Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  let C : PointedFiniteDiagram j :=
    { objects := A.objects ⊔ B.objects
      point_mem := Finset.mem_union_left _ A.point_mem
      arrows := A.arrows.image ιA ⊔ B.arrows.image ιB }
  refine ⟨C, ?_, ?_⟩
  · rintro s ⟨hsj, hs⟩
    refine ⟨hsj, ?_⟩
    intro f hf
    have hf' : ιA f ∈ C.arrows := by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    simpa [ιA] using hs hf'
  · rintro s ⟨hsj, hs⟩
    refine ⟨hsj, ?_⟩
    intro f hf
    have hf' : ιB f ∈ C.arrows := by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    simpa [ιB] using hs hf'

private theorem partialSectionsAt_closed (j : J) (x : F.obj j)
    (D : PointedFiniteDiagram j) : IsClosed (partialSectionsAt F j x D) := by
  have hEq :
      partialSectionsAt F j x D =
        {s | s j = x} ∩
          ⋂ (f : FiniteDiagramArrow D.objects) (_ : f ∈ D.arrows),
            {s | F.map f.2.2.2.2 (s f.1) = s f.2.1} := by
    ext s
    simp only [partialSectionsAt, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [hEq]
  apply IsClosed.inter
  · exact isClosed_eq (continuous_apply j) continuous_const
  · apply isClosed_biInter
    intro f _
    apply isClosed_eq <;> fun_prop

private theorem exists_limitCone_point_of_mem_eventualRange
    [IsCofilteredOrEmpty J] (j : J) (x : F.obj j)
    (hx : x ∈ (F ⋙ forget CompHausAddCommGrp).eventualRange j) :
    ∃ s : (limitCone F).pt, (limitCone F).π.app j s = x := by
  classical
  let _ : Nonempty (PointedFiniteDiagram j) :=
    ⟨{ objects := {j}
       point_mem := Finset.mem_singleton_self j
       arrows := ∅ }⟩
  obtain ⟨s, hs⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (partialSectionsAt F j x)
      (partialSectionsAt_directed F j x)
      (partialSectionsAt_nonempty F j x hx)
      (fun D => IsClosed.isCompact (partialSectionsAt_closed F j x D))
      (partialSectionsAt_closed F j x)
  have hsj : s j = x := by
    let D : PointedFiniteDiagram j :=
      { objects := {j}
        point_mem := Finset.mem_singleton_self j
        arrows := ∅ }
    exact (Set.mem_iInter.mp hs D).1
  refine ⟨⟨s, ?_⟩, hsj⟩
  intro X Y f
  let D : PointedFiniteDiagram j :=
    { objects := {j, X, Y}
      point_mem := by simp
      arrows := {⟨X, Y, by simp, by simp, f⟩} }
  exact (Set.mem_iInter.mp hs D).2 (Finset.mem_singleton_self _)

private theorem range_limitCone_projection [IsCofilteredOrEmpty J] (j : J) :
    range ((limitCone F).π.app j) =
      (F ⋙ forget CompHausAddCommGrp).eventualRange j := by
  apply Set.Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    rw [Functor.mem_eventualRange_iff]
    intro i f
    change ∃ y, F.map f y = s.1 j
    exact ⟨s.1 i, s.2 f⟩
  · intro x hx
    exact exists_limitCone_point_of_mem_eventualRange F j x hx

/-- In a cofiltered diagram of compact Hausdorff additive commutative groups,
the range of a canonical limit projection is exactly the intersection of the
ranges of all transition maps into that stage. -/
theorem limit_π_range_eq_eventualRange [IsCofilteredOrEmpty J] (j : J) :
    range (limit.π F j) =
      (F ⋙ forget CompHausAddCommGrp).eventualRange j := by
  let t : LimitCone F := ⟨limitCone F, limitConeIsLimit F⟩
  rw [← limit.isoLimitCone_hom_π t j]
  change range ((fun y => t.cone.π.app j y) ∘
    fun x => (limit.isoLimitCone t).hom x) = _
  have he : Function.Surjective (fun x => (limit.isoLimitCone t).hom x) :=
    fun y => ⟨(limit.isoLimitCone t).inv y,
      Iso.inv_hom_id_apply (limit.isoLimitCone t) y⟩
  rw [he.range_comp]
  exact range_limitCone_projection F j

/-- A canonical projection from a cofiltered compact Hausdorff additive-group
limit is surjective when the eventual range at that stage is the whole stage. -/
theorem limit_π_surjective_of_eventualRange_eq_univ [IsCofilteredOrEmpty J]
    (j : J) (h : (F ⋙ forget CompHausAddCommGrp).eventualRange j = Set.univ) :
    Function.Surjective (limit.π F j) := by
  rw [← Set.range_eq_univ]
  exact (limit_π_range_eq_eventualRange F j).trans h

/-- A canonical projection from a cofiltered compact Hausdorff additive-group
limit is surjective if every transition map into that stage is surjective. -/
theorem limit_π_surjective_of_maps_surjective [IsCofilteredOrEmpty J]
    (j : J) (h : ∀ {i : J} (f : i ⟶ j), Function.Surjective (F.map f)) :
    Function.Surjective (limit.π F j) := by
  apply limit_π_surjective_of_eventualRange_eq_univ F j
  ext x
  simp only [Functor.mem_eventualRange_iff, Set.mem_univ, iff_true]
  intro i f
  exact h f x

variable (G : J ⥤ CompHausAddCommGrp.{max u v}) (η : F ⟶ G)

noncomputable local instance :
    HasLimitsOfShape J CompHausAddCommGrp.{max u v} :=
  ⟨fun _ ↦ inferInstance⟩

private theorem limit_element_ext
    (K : J ⥤ CompHausAddCommGrp.{max u v})
    (x y : (CategoryTheory.Limits.limit K : CompHausAddCommGrp))
    (h : ∀ k, limit.π K k x = limit.π K k y) : x = y := by
  let t : LimitCone K := ⟨limitCone K, limitConeIsLimit K⟩
  let e := limit.isoLimitCone t
  apply ((forget CompHausAddCommGrp).mapIso e).toEquiv.injective
  apply Subtype.ext
  funext k
  have hx := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π t k) x
  have hy := ConcreteCategory.congr_hom (limit.isoLimitCone_hom_π t k) y
  exact hx.trans ((h k).trans hy.symm)

private def partialLiftsAt
    (t : (CategoryTheory.Limits.limit G : CompHausAddCommGrp)) (j : J)
    (D : PointedFiniteDiagram j) : Set (∀ k, F.obj k) :=
  {s | (∀ k, k ∈ D.objects → η.app k (s k) = limit.π G k t) ∧
    ∀ {f : FiniteDiagramArrow D.objects} (_ : f ∈ D.arrows),
      F.map f.2.2.2.2 (s f.1) = s f.2.1}

private theorem partialLiftsAt_nonempty [IsCofilteredOrEmpty J]
    (t : (CategoryTheory.Limits.limit G : CompHausAddCommGrp)) (j : J)
    (hη : ∀ k, ∃ y, η.app k y = limit.π G k t)
    (D : PointedFiniteDiagram j) :
    (partialLiftsAt F G η t j D).Nonempty := by
  classical
  let _ : Nonempty J := ⟨j⟩
  let _ : IsCofiltered J := ⟨⟩
  let k := IsCofiltered.inf D.objects D.arrows
  obtain ⟨y, hy⟩ := hη k
  refine ⟨fun i => if hi : i ∈ D.objects then
      F.map (IsCofiltered.infTo D.objects D.arrows hi) y else 0, ?_⟩
  constructor
  · intro i hi
    dsimp only
    rw [dite_eq_left hi]
    let q := IsCofiltered.infTo D.objects D.arrows hi
    have hnat := ConcreteCategory.congr_hom (η.naturality q) y
    have hlim := ConcreteCategory.congr_hom (limit.w G q) t
    calc
      η.app i (F.map q y) = G.map q (η.app k y) := by
        simpa only [comp_apply] using hnat
      _ = G.map q (limit.π G k t) := congrArg (G.map q) hy
      _ = limit.π G i t := by simpa only [comp_apply] using hlim
  · rintro ⟨X, Y, hX, hY, f⟩ hf
    dsimp only
    rwa [dite_eq_left hX, dite_eq_left hY, ← comp_apply, ← F.map_comp,
      @IsCofiltered.infTo_commutes _ _ _ D.objects D.arrows]

private theorem partialLiftsAt_directed
    (t : (CategoryTheory.Limits.limit G : CompHausAddCommGrp)) (j : J) :
    Directed GE.ge (partialLiftsAt F G η t j) := by
  classical
  intro A B
  let ιA : FiniteDiagramArrow A.objects →
      FiniteDiagramArrow (A.objects ⊔ B.objects) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1,
      Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : FiniteDiagramArrow B.objects →
      FiniteDiagramArrow (A.objects ⊔ B.objects) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1,
      Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  let C : PointedFiniteDiagram j :=
    { objects := A.objects ⊔ B.objects
      point_mem := Finset.mem_union_left _ A.point_mem
      arrows := A.arrows.image ιA ⊔ B.arrows.image ιB }
  refine ⟨C, ?_, ?_⟩
  · rintro s ⟨hsη, hs⟩
    refine ⟨fun k hk ↦ hsη k (Finset.mem_union_left _ hk), ?_⟩
    intro f hf
    have hf' : ιA f ∈ C.arrows := by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    simpa [ιA] using hs hf'
  · rintro s ⟨hsη, hs⟩
    refine ⟨fun k hk ↦ hsη k (Finset.mem_union_right _ hk), ?_⟩
    intro f hf
    have hf' : ιB f ∈ C.arrows := by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨f, hf, rfl⟩
    simpa [ιB] using hs hf'

private theorem partialLiftsAt_closed
    (t : (CategoryTheory.Limits.limit G : CompHausAddCommGrp)) (j : J)
    (D : PointedFiniteDiagram j) : IsClosed (partialLiftsAt F G η t j D) := by
  have hEq :
      partialLiftsAt F G η t j D =
        (⋂ (k : J) (_ : k ∈ D.objects),
          {s | η.app k (s k) = limit.π G k t}) ∩
        ⋂ (f : FiniteDiagramArrow D.objects) (_ : f ∈ D.arrows),
          {s | F.map f.2.2.2.2 (s f.1) = s f.2.1} := by
    ext s
    simp only [partialLiftsAt, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [hEq]
  apply IsClosed.inter
  · apply isClosed_biInter
    intro k _
    exact isClosed_eq
      ((η.app k).hom.continuous.comp (continuous_apply k)) continuous_const
  · apply isClosed_biInter
    intro f _
    apply isClosed_eq <;> fun_prop

private theorem exists_limitCone_lift [IsCofilteredOrEmpty J]
    (t : (CategoryTheory.Limits.limit G : CompHausAddCommGrp)) (j : J)
    (hη : ∀ k, ∃ y, η.app k y = limit.π G k t) :
    ∃ s : (limitCone F).pt,
      ∀ k, η.app k ((limitCone F).π.app k s) = limit.π G k t := by
  classical
  let _ : Nonempty (PointedFiniteDiagram j) :=
    ⟨{ objects := {j}
       point_mem := Finset.mem_singleton_self j
       arrows := ∅ }⟩
  obtain ⟨s, hs⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (partialLiftsAt F G η t j)
      (partialLiftsAt_directed F G η t j)
      (partialLiftsAt_nonempty F G η t j hη)
      (fun D => IsClosed.isCompact (partialLiftsAt_closed F G η t j D))
      (partialLiftsAt_closed F G η t j)
  refine ⟨⟨s, ?_⟩, ?_⟩
  · intro X Y f
    let D : PointedFiniteDiagram j :=
      { objects := {j, X, Y}
        point_mem := by simp
        arrows := {⟨X, Y, by simp, by simp, f⟩} }
    exact (Set.mem_iInter.mp hs D).2 (Finset.mem_singleton_self _)
  · intro k
    let D : PointedFiniteDiagram j :=
      { objects := {j, k}
        point_mem := by simp
        arrows := ∅ }
    exact (Set.mem_iInter.mp hs D).1 k
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))

private theorem exists_limit_map_preimage_of_nonempty [IsCofilteredOrEmpty J]
    [Nonempty J] (t : (CategoryTheory.Limits.limit G : CompHausAddCommGrp))
    (hη : ∀ k, ∃ y, η.app k y = limit.π G k t) :
    ∃ x, lim.map η x = t := by
  let j : J := Classical.choice ‹Nonempty J›
  obtain ⟨s, hs⟩ := exists_limitCone_lift F G η t j hη
  let tF : LimitCone F := ⟨limitCone F, limitConeIsLimit F⟩
  let x : (CategoryTheory.Limits.limit F : CompHausAddCommGrp) :=
    (limit.isoLimitCone tF).inv s
  refine ⟨x, ?_⟩
  have hπ : ∀ k, limit.π G k (lim.map η x) = limit.π G k t := by
    intro k
    calc
      limit.π G k (lim.map η x) = η.app k (limit.π F k x) :=
        ConcreteCategory.congr_hom (limit.map_π η k) x
      _ = η.app k ((limitCone F).π.app k s) := by
        congr 1
        exact ConcreteCategory.congr_hom (limit.isoLimitCone_inv_π tF k) s
      _ = limit.π G k t := hs k
  exact limit_element_ext G _ _ hπ

private theorem limit_map_surjective_of_nonempty [IsCofilteredOrEmpty J]
    [Nonempty J] (hη : ∀ k, Function.Surjective (η.app k)) :
    Function.Surjective (lim.map η) := by
  intro t
  exact exists_limit_map_preimage_of_nonempty F G η t
    (fun k ↦ hη k (limit.π G k t))

/-- A pointwise-surjective natural transformation between cofiltered diagrams
of compact Hausdorff additive commutative groups induces a surjective map on
their limits. -/
theorem limit_map_surjective [IsCofilteredOrEmpty J]
    (hη : ∀ k, Function.Surjective (η.app k)) :
    Function.Surjective (lim.map η) := by
  cases isEmpty_or_nonempty J with
  | inl h =>
      let _ := h
      intro y
      let t : LimitCone G := ⟨limitCone G, limitConeIsLimit G⟩
      refine ⟨0, ?_⟩
      let e := limit.isoLimitCone t
      apply ((forget CompHausAddCommGrp).mapIso e).toEquiv.injective
      apply Subtype.ext
      funext j
      exact isEmptyElim j
  | inr h =>
      let _ := h
      exact limit_map_surjective_of_nonempty F G η hη

variable (H : J ⥤ CompHausAddCommGrp.{max u v}) (θ : G ⟶ H)

/-- Pointwise exact natural transformations between cofiltered diagrams of
compact Hausdorff additive commutative groups induce exact maps on their
limits. -/
theorem limit_map_exact [IsCofilteredOrEmpty J]
    (h : ∀ k, Function.Exact (η.app k) (θ.app k)) :
    Function.Exact (lim.map η) (lim.map θ) := by
  intro t
  constructor
  · intro ht
    cases isEmpty_or_nonempty J with
    | inl hJ =>
        let _ := hJ
        refine ⟨0, ?_⟩
        apply limit_element_ext G
        intro k
        exact isEmptyElim k
    | inr hJ =>
        let _ := hJ
        apply exists_limit_map_preimage_of_nonempty F G η t
        intro k
        apply (h k (limit.π G k t)).mp
        calc
          θ.app k (limit.π G k t) = limit.π H k (lim.map θ t) :=
            (ConcreteCategory.congr_hom (limit.map_π θ k) t).symm
          _ = limit.π H k 0 := congrArg (limit.π H k) ht
          _ = 0 := (limit.π H k).hom.map_zero
  · rintro ⟨s, rfl⟩
    apply limit_element_ext H
    intro k
    calc
      limit.π H k (lim.map θ (lim.map η s)) =
          θ.app k (limit.π G k (lim.map η s)) :=
        ConcreteCategory.congr_hom (limit.map_π θ k) (lim.map η s)
      _ = θ.app k (η.app k (limit.π F k s)) := by
        exact congrArg (θ.app k)
          (ConcreteCategory.congr_hom (limit.map_π η k) s)
      _ = 0 := (h k).apply_apply_eq_zero _
      _ = limit.π H k 0 := (limit.π H k).hom.map_zero.symm

end CompHausAddCommGrp
