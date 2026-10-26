/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteStageImages
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Whiskering

/-!
# Maps from a cofiltered limit to a finite discrete space

For a diagram of finite discrete spaces, maps from a limiting cone to a finite
target arise from maps at finite stages. Stage maps form a filtered colimit:
two representatives agree precisely when they agree after a common refinement.

The index belongs to `Type u` and the finite stages and target to
`FintypeCat.{max u w}`. The nonempty cofiltered assumption matters: an empty
index has a one-point limit but an empty stage-hom colimit, even for the
one-point target. Empty finite stages and targets are allowed.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1
  (inverse-system/pro-category motivation, not a stated Lean-level Hom equivalence).
- Mathlib, `Mathlib.CategoryTheory.Limits.Types.Filtered` and
  `Mathlib.CategoryTheory.Whiskering` (filtered colimits and stage-map functoriality);
  `FiniteStageImages` supplies finite-stage equality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    (F : I ⥤ FintypeCat.{max u w})

/-- Maps out of finite stages, with transition maps given by precomposition
along refinements. -/
abbrev stageHom (S : FintypeCat.{max u w}) : Iᵒᵖ ⥤ Type (max u w) :=
  F.op ⋙ yoneda.obj S

/-- The class represented by a map out of one finite stage. -/
noncomputable def stageHomClass (S : FintypeCat.{max u w}) (i : I) (g : F.obj i ⟶ S) :
    colimit (stageHom F S) :=
  colimit.ι (stageHom F S) (Opposite.op i) g

omit [IsCofiltered I] in
@[simp]
theorem stageHomClass_refine (S : FintypeCat.{max u w}) {i j : I}
    (a : j ⟶ i) (g : F.obj i ⟶ S) :
    stageHomClass F S i g = stageHomClass F S j (F.map a ≫ g) := by
  exact (colimit.w_apply (stageHom F S) a.op g).symm

/-- Two stage maps have the same colimit class exactly when they agree after
one common refinement. -/
theorem stageHomClass_eq_iff (S : FintypeCat.{max u w}) (i k : I)
    (g : F.obj i ⟶ S) (h : F.obj k ⟶ S) :
    stageHomClass F S i g = stageHomClass F S k h ↔
      ∃ (j : I) (a : j ⟶ i) (b : j ⟶ k), F.map a ≫ g = F.map b ≫ h := by
  constructor
  · intro heq
    obtain ⟨j, a, b, hab⟩ :=
      (Limits.Types.FilteredColimit.colimit_eq_iff (stageHom F S)).1 heq
    refine ⟨j.unop, a.unop, b.unop, ?_⟩
    change F.map a.unop ≫ g = F.map b.unop ≫ h at hab
    exact hab
  · rintro ⟨j, a, b, hab⟩
    apply (Limits.Types.FilteredColimit.colimit_eq_iff (stageHom F S)).2
    refine ⟨Opposite.op j, a.op, b.op, ?_⟩
    change F.map a ≫ g = F.map b ≫ h
    exact hab

variable {F}

/-- A cocone of continuous maps, obtained by composing a stage map with its
projection from a cone. No limiting property is needed. -/
def stageHomCocone (c : Cone (F ⋙ FintypeCat.toProfinite))
    (S : FintypeCat.{max u w}) : Cocone (stageHom F S) where
  pt := c.pt ⟶ FintypeCat.toProfinite.obj S
  ι :=
    { app i := by
        cases i with
        | op i =>
          exact ↾fun (g : F.obj i ⟶ S) =>
            c.π.app i ≫ FintypeCat.toProfinite.map g
      naturality := by
        intro i j a
        cases i with
        | op i =>
          cases j with
          | op j =>
            ext g
            change c.π.app j ≫
              FintypeCat.toProfinite.map (F.map a.unop ≫ g) =
              c.π.app i ≫ FintypeCat.toProfinite.map g
            rw [FintypeCat.toProfinite.map_comp, ← Category.assoc]
            exact congrArg (fun h => h ≫ FintypeCat.toProfinite.map g) (c.w a.unop) }

/-- Descent from a filtered colimit of stage maps to continuous maps from
the cone point. This construction works for any cone. -/
noncomputable def stageHomToContinuous (c : Cone (F ⋙ FintypeCat.toProfinite))
    (S : FintypeCat.{max u w}) :
    colimit (stageHom F S) → (c.pt ⟶ FintypeCat.toProfinite.obj S) :=
  colimit.desc (stageHom F S) (stageHomCocone c S)

omit [IsCofiltered I] in
@[simp]
theorem stageHomToContinuous_class (c : Cone (F ⋙ FintypeCat.toProfinite))
    (S : FintypeCat.{max u w}) (i : I) (g : F.obj i ⟶ S) :
    stageHomToContinuous c S (stageHomClass F S i g) =
      c.π.app i ≫ FintypeCat.toProfinite.map g := by
  exact colimit.ι_desc_apply (stageHomCocone c S) (Opposite.op i) g

/-- For a limiting cone, descent is bijective. -/
theorem stageHomToContinuous_bijective (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w}) :
    Function.Bijective (stageHomToContinuous c S) := by
  constructor
  · intro x y heq
    obtain ⟨i, g, rfl⟩ := Limits.Types.jointly_surjective' x
    obtain ⟨k, h, rfl⟩ := Limits.Types.jointly_surjective' y
    cases i with
    | op i =>
      cases k with
      | op k =>
        change (F.obj i ⟶ S) at g
        change (F.obj k ⟶ S) at h
        change stageHomToContinuous c S (stageHomClass F S i g) =
          stageHomToContinuous c S (stageHomClass F S k h) at heq
        rw [stageHomToContinuous_class, stageHomToContinuous_class] at heq
        have heval : ∀ p : c.pt, g (c.π.app i p) = h (c.π.app k p) := by
          intro p
          exact congrArg (fun f : c.pt ⟶ FintypeCat.toProfinite.obj S => f p) heq
        obtain ⟨j, a, b, hab⟩ :=
          exists_common_stage_map_eq_of_limit_eq c hc i k g h heval
        apply (stageHomClass_eq_iff F S i k g h).2
        refine ⟨j, a, b, ?_⟩
        ext p
        exact hab p
  · intro f
    obtain ⟨i, g, rfl⟩ := exists_hom c hc f
    exact ⟨stageHomClass F S i g, stageHomToContinuous_class c S i g⟩

/-- Continuous maps to a finite discrete space are the colimit of maps
from finite stages.

This uses Mathlib’s filtered-colimit construction and `FiniteStageImages`; the pro-category
discussion in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 is
motivation, not a printed Hom equivalence. -/
noncomputable def stageHomEquiv (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w}) :
    colimit (stageHom F S) ≃ (c.pt ⟶ FintypeCat.toProfinite.obj S) :=
  Equiv.ofBijective (stageHomToContinuous c S)
    (stageHomToContinuous_bijective c hc S)

@[simp]
theorem stageHomEquiv_apply (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w}) (x : colimit (stageHom F S)) :
    stageHomEquiv c hc S x = stageHomToContinuous c S x := rfl

@[simp]
theorem stageHomEquiv_apply_class (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w}) (i : I) (g : F.obj i ⟶ S) :
    stageHomEquiv c hc S (stageHomClass F S i g) =
      c.π.app i ≫ FintypeCat.toProfinite.map g := by
  simp

@[simp]
theorem stageHomEquiv_symm_apply (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w})
    (f : c.pt ⟶ FintypeCat.toProfinite.obj S) :
    stageHomToContinuous c S ((stageHomEquiv c hc S).symm f) = f :=
  (stageHomEquiv c hc S).apply_symm_apply f

@[simp]
theorem stageHomEquiv_symm_apply_projection
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (S : FintypeCat.{max u w}) (i : I) (g : F.obj i ⟶ S) :
    (stageHomEquiv c hc S).symm
      (c.π.app i ≫ FintypeCat.toProfinite.map g) = stageHomClass F S i g := by
  apply (stageHomEquiv c hc S).injective
  simp

/-- Two classes coincide if their continuous maps coincide. -/
theorem stageHomClass_ext (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w})
    {x y : colimit (stageHom F S)}
    (h : stageHomToContinuous c S x = stageHomToContinuous c S y) : x = y :=
  (stageHomToContinuous_bijective c hc S).1 h

/-- Every continuous map to a finite discrete target factors through a
finite stage. -/
theorem exists_stageHomClass (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) (S : FintypeCat.{max u w})
    (f : c.pt ⟶ FintypeCat.toProfinite.obj S) :
    ∃ (i : I) (g : F.obj i ⟶ S),
      stageHomToContinuous c S (stageHomClass F S i g) = f := by
  obtain ⟨i, g, rfl⟩ := exists_hom c hc f
  exact ⟨i, g, stageHomToContinuous_class c S i g⟩

variable {S T : FintypeCat.{max u w}}

/-- Postcomposition at finite stages is functorial on colimits. -/
noncomputable def stageHomFunctor (F : I ⥤ FintypeCat.{max u w}) :
    FintypeCat.{max u w} ⥤ Type (max u w) :=
  yoneda ⋙ (Functor.whiskeringLeft Iᵒᵖ FintypeCat.{max u w}ᵒᵖ
    (Type (max u w))).obj F.op ⋙ colim

/-- Target postcomposition on the filtered colimit of stage maps. -/
noncomputable def stageHomPost (t : S ⟶ T) :
    colimit (stageHom F S) ⟶ colimit (stageHom F T) :=
  (stageHomFunctor F).map t

omit [IsCofiltered I] in
@[simp]
theorem stageHomPost_class (t : S ⟶ T) (i : I) (g : F.obj i ⟶ S) :
    stageHomPost t (stageHomClass F S i g) = stageHomClass F T i (g ≫ t) := by
  exact colimit.ι_map_apply (Functor.whiskerLeft F.op (yoneda.map t)) (Opposite.op i) g

omit [IsCofiltered I] in
theorem stageHomToContinuous_naturality (c : Cone (F ⋙ FintypeCat.toProfinite))
    {S T : FintypeCat.{max u w}} (t : S ⟶ T)
    (x : colimit (stageHom F S)) :
    stageHomToContinuous c T (stageHomPost t x) =
      stageHomToContinuous c S x ≫ FintypeCat.toProfinite.map t := by
  obtain ⟨i, g, rfl⟩ := Limits.Types.jointly_surjective' x
  cases i with
  | op i =>
    change stageHomToContinuous c T (stageHomPost t (stageHomClass F S i g)) =
      stageHomToContinuous c S (stageHomClass F S i g) ≫
        FintypeCat.toProfinite.map t
    simp only [stageHomPost_class, stageHomToContinuous_class,
      FintypeCat.toProfinite.map_comp, Category.assoc]

/-- The comparison is natural in the finite target. -/
noncomputable def stageHomNatIso (c : Cone (F ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    stageHomFunctor F ≅ FintypeCat.toProfinite ⋙ coyoneda.obj (Opposite.op c.pt) :=
  NatIso.ofComponents
    (fun S => (stageHomEquiv c hc S).toIso)
    (by
      intro S T t
      ext x
      exact stageHomToContinuous_naturality c t x)

@[simp]
theorem stageHomNatIso_hom_app_apply_class
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c)
    (S : FintypeCat.{max u w}) (i : I) (g : F.obj i ⟶ S) :
    (stageHomNatIso c hc).hom.app S (stageHomClass F S i g) =
      c.π.app i ≫ FintypeCat.toProfinite.map g := by
  exact stageHomEquiv_apply_class c hc S i g

end Profinite
