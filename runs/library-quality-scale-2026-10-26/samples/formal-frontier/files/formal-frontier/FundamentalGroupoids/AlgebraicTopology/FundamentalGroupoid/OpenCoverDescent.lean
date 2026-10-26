/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.CategoryTheory.Category.Pairwise
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.OpenCover
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCover

/-!
# Strict fundamental-groupoid descent over open covers

The pairwise diagram of an indexed family of opens has one object for every chart and
one for every ordered pairwise intersection. Its maps are inclusions from intersections
to charts. There is no object for an intersection of the empty family.

Strictly compatible local functors extend uniquely to the fundamental groupoid of the
covered space. Compatibility and restriction mean equality of functors, not specified
natural isomorphisms. The target may be any category, with object and morphism universes
unrelated to those of the space or the index. The same universal property is expressed
by colimit cocones in `Grpd` and `Cat` at their fixed bundled sizes.

## Scope

No connectedness, inhabited-intersection, nonempty-target or faithful-inclusion
hypothesis is part of the statements. Based fundamental groups and wedges are separate.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7, printed p. 17.
  The arbitrary indexed cover and arbitrary target category here generalize the
  path-connected, intersection-closed groupoid diagram in that source.
* Mathlib's fundamental groupoids, by Shing Tak Lam; pairwise diagrams and open-subspace
  functors, by Kim Morrison; open covers, by David Loeffler; equality transport and
  colimit APIs in `CategoryTheory`.
-/

@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The diagram of fundamental groupoids of charts and pairwise intersections. -/
def openCoverDiagram (U : ι → Opens X) : Pairwise ι ⥤ Grpd.{u, u} :=
  (Pairwise.diagram U ⋙ Opens.toTopCat (TopCat.of X)) ⋙ fundamentalGroupoidFunctor

/-- A singleton of the pairwise diagram is the fundamental groupoid of that chart. -/
@[simp]
theorem openCoverDiagram_obj_single (U : ι → Opens X) (i : ι) :
    (openCoverDiagram U).obj (.single i) = Grpd.of (FundamentalGroupoid (U i)) := rfl

/-- A pair of the diagram is the fundamental groupoid of the intersection, possibly empty. -/
@[simp]
theorem openCoverDiagram_obj_pair (U : ι → Opens X) (i j : ι) :
    (openCoverDiagram U).obj (.pair i j) =
      Grpd.of (FundamentalGroupoid (U i ⊓ U j : Opens X)) := rfl

/-- The left edge is induced by the inclusion of the intersection into its first chart. -/
@[simp]
theorem openCoverDiagram_map_left (U : ι → Opens X) (i j : ι) :
    (openCoverDiagram U).map (Pairwise.Hom.left i j) =
      map (((Opens.toTopCat (TopCat.of X)).map (Opens.infLELeft (U i) (U j))).hom) := rfl

/-- The right edge is induced by the inclusion of the intersection into its second chart. -/
@[simp]
theorem openCoverDiagram_map_right (U : ι → Opens X) (i j : ι) :
    (openCoverDiagram U).map (Pairwise.Hom.right i j) =
      map (((Opens.toTopCat (TopCat.of X)).map (Opens.infLERight (U i) (U j))).hom) := rfl

/-- The inclusion cocone from the pairwise diagram to the ambient fundamental groupoid. -/
def openCoverCocone (U : ι → Opens X) : Cocone (openCoverDiagram U) where
  pt := Grpd.of (FundamentalGroupoid X)
  ι :=
    { app := fun k =>
        map (Opens.inclusion' (X := TopCat.of X) ((Pairwise.diagram U).obj k)).hom
      naturality := by
        intro a b f
        change map (((Opens.toTopCat (TopCat.of X)).map ((Pairwise.diagram U).map f)).hom) ⋙
            map (Opens.inclusion' (X := TopCat.of X) ((Pairwise.diagram U).obj b)).hom =
          map (Opens.inclusion' (X := TopCat.of X) ((Pairwise.diagram U).obj a)).hom
        rw [← FundamentalGroupoid.map_comp]
        rfl }

/-- The inclusion cocone has the ambient fundamental groupoid as its vertex. -/
@[simp]
theorem openCoverCocone_pt (U : ι → Opens X) :
    (openCoverCocone U).pt = Grpd.of (FundamentalGroupoid X) := rfl

/-- Every leg of the cocone is induced by the corresponding open-subspace inclusion. -/
theorem openCoverCocone_ι_app (U : ι → Opens X) (k : Pairwise ι) :
    (openCoverCocone U).ι.app k =
      map (Opens.inclusion' (X := TopCat.of X) ((Pairwise.diagram U).obj k)).hom := rfl

/-- The chart legs are the usual functors induced by subtype inclusion. -/
@[simp]
theorem openCoverCocone_ι_app_single (U : ι → Opens X) (i : ι) :
    (openCoverCocone U).ι.app (.single i) = map (ContinuousMap.subtypeVal (U i : Set X)) := rfl

/-- The intersection legs are induced by inclusion of the intersection in the ambient space. -/
@[simp]
theorem openCoverCocone_ι_app_pair (U : ι → Opens X) (i j : ι) :
    (openCoverCocone U).ι.app (.pair i j) =
      map (ContinuousMap.subtypeVal (↑(U i ⊓ U j) : Set X)) := rfl

/-- The same pairwise diagram, regarded as a diagram in the category of categories. -/
def openCoverCatDiagram (U : ι → Opens X) : Pairwise ι ⥤ Cat.{u, u} :=
  openCoverDiagram U ⋙ Grpd.forgetToCat

/-- The category at a diagram object is its underlying category as a groupoid. -/
@[simp]
theorem openCoverCatDiagram_obj (U : ι → Opens X) (k : Pairwise ι) :
    (openCoverCatDiagram U).obj k = Cat.of ((openCoverDiagram U).obj k) := rfl

/-- The category-valued diagram maps wrap the same inclusion functors. -/
@[simp]
theorem openCoverCatDiagram_map (U : ι → Opens X) {a b : Pairwise ι} (f : a ⟶ b) :
    (openCoverCatDiagram U).map f = ((openCoverDiagram U).map f).toCatHom := rfl

/-- The inclusion cocone regarded as a cocone in `Cat`, with functors as morphisms. -/
def openCoverCatCocone (U : ι → Opens X) : Cocone (openCoverCatDiagram U) :=
  Grpd.forgetToCat.mapCocone (openCoverCocone U)

/-- The category-valued inclusion cocone has the ambient fundamental groupoid as its vertex. -/
@[simp]
theorem openCoverCatCocone_pt (U : ι → Opens X) :
    (openCoverCatCocone U).pt = Cat.of (FundamentalGroupoid X) := rfl

/-- All legs of the category-valued cocone wrap the corresponding groupoid-valued legs. -/
theorem openCoverCatCocone_ι_app (U : ι → Opens X) (k : Pairwise ι) :
    (openCoverCatCocone U).ι.app k = ((openCoverCocone U).ι.app k).toCatHom := rfl

/-- The singleton legs in `Cat` wrap the same strict inclusion functors. -/
@[simp]
theorem openCoverCatCocone_ι_app_single (U : ι → Opens X) (i : ι) :
    (openCoverCatCocone U).ι.app (.single i) =
      (map (ContinuousMap.subtypeVal (U i : Set X))).toCatHom := rfl

/-- The intersection legs in `Cat` wrap inclusion from the pairwise intersection. -/
@[simp]
theorem openCoverCatCocone_ι_app_pair (U : ι → Opens X) (i j : ι) :
    (openCoverCatCocone U).ι.app (.pair i j) =
      (map (ContinuousMap.subtypeVal (↑(U i ⊓ U j) : Set X))).toCatHom := rfl

variable {U : ι → Opens X} {D : Type w} [Category.{w'} D]

section HomotopyCells

open scoped unitInterval

variable (H : C(I × I, X)) (i : ι) (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d)
  (hsmall : Set.Icc a b ×ˢ Set.Icc c d ⊆ H ⁻¹' (U i : Set X))

-- Normalize a chart-contained rectangle, allowing either side length to be zero.
private def affineCell : C(I × I, U i) where
  toFun z := ⟨H (Set.Icc.convexComb a b z.1, Set.Icc.convexComb c d z.2),
    hsmall ⟨⟨Set.Icc.le_convexComb hab z.1, Set.Icc.convexComb_le hab z.1⟩,
      ⟨Set.Icc.le_convexComb hcd z.2, Set.Icc.convexComb_le hcd z.2⟩⟩⟩
  continuous_toFun :=
    (H.continuous.comp (((Set.Icc.continuous_convexComb a b).comp continuous_fst).prodMk
      ((Set.Icc.continuous_convexComb c d).comp continuous_snd))).subtype_mk _

private theorem affineCell_zero_left (s : I) :
    (affineCell H i a b c d hab hcd hsmall (0, s) : X) =
      H (a, Set.Icc.convexComb c d s) := by
  simp [affineCell]

private theorem affineCell_one_left (s : I) :
    (affineCell H i a b c d hab hcd hsmall (1, s) : X) =
      H (b, Set.Icc.convexComb c d s) := by
  simp [affineCell]

private theorem affineCell_zero_right (s : I) :
    (affineCell H i a b c d hab hcd hsmall (s, 0) : X) =
      H (Set.Icc.convexComb a b s, c) := by
  simp [affineCell]

private theorem affineCell_one_right (s : I) :
    (affineCell H i a b c d hab hcd hsmall (s, 1) : X) =
      H (Set.Icc.convexComb a b s, d) := by
  simp [affineCell]

-- The first coordinate is the homotopy parameter, as in `Path.Homotopy`.
private def cellHomotopy {Y : Type*} [TopologicalSpace Y] (K : C(I × I, Y)) :
    (K.curry 0).Homotopy (K.curry 1) where
  toContinuousMap := K
  map_zero_left _ := rfl
  map_one_left _ := rfl

-- Apply only a functor on the cell's codomain; no global descent map is used.
private theorem cell_commSq {Y : Type*} [TopologicalSpace Y]
    (K : C(I × I, Y)) (F : FundamentalGroupoid Y ⥤ D) :
    CommSq
      (F.map (fromPath (Path.Homotopic.Quotient.mk
        (Path.id.map (K.curry 0).continuous))))
      (F.map (fromPath (Path.Homotopic.Quotient.mk ((cellHomotopy K).evalAt 0))))
      (F.map (fromPath (Path.Homotopic.Quotient.mk ((cellHomotopy K).evalAt 1))))
      (F.map (fromPath (Path.Homotopic.Quotient.mk
        (Path.id.map (K.curry 1).continuous)))) := by
  apply F.map_commSq
  exact ⟨Path.Homotopic.Quotient.eq.mpr
    (Path.Homotopic.map_trans_evalAt (cellHomotopy K) Path.id)⟩

end HomotopyCells

private theorem descentObj_overlap
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i j : ι) (x : X) (hi : x ∈ U i) (hj : x ∈ U j) :
    (F i).obj (mk ⟨x, hi⟩) = (F j).obj (mk ⟨x, hj⟩) :=
  CategoryTheory.Functor.congr_obj (hF i j)
    (mk (⟨x, hi, hj⟩ : (U i ⊓ U j : Opens X)))

-- The cover lift chooses a chart only at a supplied point, also when the space is empty.
private noncomputable def descentObj (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j) (x : X) : D :=
  Set.liftCover (fun i => (U i : Set X)) (fun i a => (F i).obj (mk a))
    (descentObj_overlap F hF) hU.iSup_set_eq_univ x

private theorem descentObj_eq (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) (x : X) (hx : x ∈ U i) :
    descentObj hU F hF x = (F i).obj (mk ⟨x, hx⟩) :=
  Set.liftCover_of_mem (S := fun i => (U i : Set X))
    (f := fun i a => (F i).obj (mk a)) (hf := descentObj_overlap F hF)
    (hS := hU.iSup_set_eq_univ) (i := i) (x := x) hx

-- Corestriction keeps the ambient endpoints, using their membership in the path range.
private def descentLocalPath {a b : X} (p : Path a b) {s : Set X}
    (hp : Set.range p ⊆ s) :
    Path (⟨a, hp p.source_mem_range⟩ : s) ⟨b, hp p.target_mem_range⟩ where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

private theorem descentLocalPath_apply {a b : X} (p : Path a b) {s : Set X}
    (hp : Set.range p ⊆ s) (t : unitInterval) :
    (descentLocalPath p hp) t = ⟨p t, hp ⟨t, rfl⟩⟩ := rfl

private theorem descentLocalPath_map_subtypeVal {a b : X} (p : Path a b)
    {s : Set X} (hp : Set.range p ⊆ s) :
    (descentLocalPath p hp).map continuous_subtype_val = p := by
  ext t
  rfl

private theorem descentLocalPath_map_left (i j : ι) {a b : X} (p : Path a b)
    (hi : Set.range p ⊆ U i) (hj : Set.range p ⊆ U j) :
    ((openCoverDiagram U).map (Pairwise.Hom.left i j)).map
        (fromPath (Path.Homotopic.Quotient.mk
          (descentLocalPath p (s := (U i ⊓ U j : Opens X))
            (fun _ hx => ⟨hi hx, hj hx⟩)))) =
      fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hi)) := by
  let f : C((U i ⊓ U j : Opens X), U i) :=
    ContinuousMap.inclusion
      (show (↑(U i ⊓ U j) : Set X) ⊆ (U i : Set X) from Set.inter_subset_left)
  change (map f).map
      (fromPath (Path.Homotopic.Quotient.mk
        (descentLocalPath p (s := (U i ⊓ U j : Opens X))
          (fun _ hx => ⟨hi hx, hj hx⟩)))) =
    fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hi))
  have hpath :
      (descentLocalPath p (s := (U i ⊓ U j : Opens X))
        (fun _ hx => ⟨hi hx, hj hx⟩)).map f.continuous =
        descentLocalPath p hi := by
    ext t
    rfl
  exact (map_fromPath_mk f
    (descentLocalPath p (s := (U i ⊓ U j : Opens X))
      (fun _ hx => ⟨hi hx, hj hx⟩))).trans
        (congrArg (fun q : Path (⟨a, hi p.source_mem_range⟩ : U i)
          ⟨b, hi p.target_mem_range⟩ => fromPath (Path.Homotopic.Quotient.mk q)) hpath)

private theorem descentLocalPath_map_right (i j : ι) {a b : X} (p : Path a b)
    (hi : Set.range p ⊆ U i) (hj : Set.range p ⊆ U j) :
    ((openCoverDiagram U).map (Pairwise.Hom.right i j)).map
        (fromPath (Path.Homotopic.Quotient.mk
          (descentLocalPath p (s := (U i ⊓ U j : Opens X))
            (fun _ hx => ⟨hi hx, hj hx⟩)))) =
      fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hj)) := by
  let f : C((U i ⊓ U j : Opens X), U j) :=
    ContinuousMap.inclusion
      (show (↑(U i ⊓ U j) : Set X) ⊆ (U j : Set X) from Set.inter_subset_right)
  change (map f).map
      (fromPath (Path.Homotopic.Quotient.mk
        (descentLocalPath p (s := (U i ⊓ U j : Opens X))
          (fun _ hx => ⟨hi hx, hj hx⟩)))) =
    fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hj))
  have hpath :
      (descentLocalPath p (s := (U i ⊓ U j : Opens X))
        (fun _ hx => ⟨hi hx, hj hx⟩)).map f.continuous =
        descentLocalPath p hj := by
    ext t
    rfl
  exact (map_fromPath_mk f
    (descentLocalPath p (s := (U i ⊓ U j : Opens X))
      (fun _ hx => ⟨hi hx, hj hx⟩))).trans
        (congrArg (fun q : Path (⟨a, hj p.source_mem_range⟩ : U j)
          ⟨b, hj p.target_mem_range⟩ => fromPath (Path.Homotopic.Quotient.mk q)) hpath)

private noncomputable def descentLocalValue (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : X} (p : Path a b) (hp : Set.range p ⊆ U i) :
    descentObj hU F hF a ⟶ descentObj hU F hF b :=
  eqToHom (descentObj_eq hU F hF i a (hp p.source_mem_range)) ≫
    (F i).map (fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hp))) ≫
      eqToHom (descentObj_eq hU F hF i b (hp p.target_mem_range)).symm

private theorem descentLocalValue_eq (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : X} (p : Path a b) (hp : Set.range p ⊆ U i) :
    descentLocalValue hU F hF i p hp =
      eqToHom (descentObj_eq hU F hF i a (hp p.source_mem_range)) ≫
        (F i).map (fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hp))) ≫
          eqToHom (descentObj_eq hU F hF i b (hp p.target_mem_range)).symm := rfl

private theorem descentLocalValue_label_independent (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i j : ι) {a b : X} (p : Path a b)
    (hi : Set.range p ⊆ U i) (hj : Set.range p ⊆ U j) :
    descentLocalValue hU F hF i p hi = descentLocalValue hU F hF j p hj := by
  have hmap :
      (F i).map (fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hi))) =
        eqToHom (descentObj_overlap F hF i j a
          (hi p.source_mem_range) (hj p.source_mem_range)) ≫
          (F j).map (fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hj))) ≫
            eqToHom (descentObj_overlap F hF i j b
              (hi p.target_mem_range) (hj p.target_mem_range)).symm := by
    let L : FundamentalGroupoid (U i ⊓ U j : Opens X) ⥤ FundamentalGroupoid (U i) :=
      (openCoverDiagram U).map (Pairwise.Hom.left i j)
    let R : FundamentalGroupoid (U i ⊓ U j : Opens X) ⥤ FundamentalGroupoid (U j) :=
      (openCoverDiagram U).map (Pairwise.Hom.right i j)
    let q : Path (⟨a, hi p.source_mem_range, hj p.source_mem_range⟩ :
        (U i ⊓ U j : Opens X)) ⟨b, hi p.target_mem_range, hj p.target_mem_range⟩ :=
      descentLocalPath p (s := (U i ⊓ U j : Opens X))
        (fun _ hx => ⟨hi hx, hj hx⟩)
    have hleft : L.map (fromPath (Path.Homotopic.Quotient.mk q)) =
        fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hi)) :=
      descentLocalPath_map_left i j p hi hj
    have hright : R.map (fromPath (Path.Homotopic.Quotient.mk q)) =
        fromPath (Path.Homotopic.Quotient.mk (descentLocalPath p hj)) :=
      descentLocalPath_map_right i j p hi hj
    have hc :
        (F i).map (L.map (fromPath (Path.Homotopic.Quotient.mk q))) =
          eqToHom (descentObj_overlap F hF i j a
            (hi p.source_mem_range) (hj p.source_mem_range)) ≫
            (F j).map (R.map (fromPath (Path.Homotopic.Quotient.mk q))) ≫
              eqToHom (descentObj_overlap F hF i j b
                (hi p.target_mem_range) (hj p.target_mem_range)).symm :=
      CategoryTheory.Functor.congr_hom
        (show L ⋙ F i = R ⋙ F j from hF i j)
        (fromPath (Path.Homotopic.Quotient.mk q))
    rw [hleft, hright] at hc
    exact hc
  rw [descentLocalValue_eq, descentLocalValue_eq, hmap]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

section WordEvaluation

variable (hU : IsOpenCover U)
  (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
  (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
    (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
  {a b : X} (p : Path a b)

-- The finite composite uses only the adjacent local values, not an ordering of the cuts.
private noncomputable def descentWord {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    ComposableArrows D n :=
  ComposableArrows.mkOfObjOfMapSucc (fun j => descentObj hU F hF (p (t j)))
    (fun j => descentLocalValue hU F hF (label j)
      (p.subpath (t j.castSucc) (t j.succ)) (hp j))

private theorem descentWord_obj {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (j : Fin (n + 1)) :
    (descentWord hU F hF p t label hp).obj j = descentObj hU F hF (p (t j)) := rfl

private theorem descentWord_map_succ {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (j : ℕ) (hj : j < n) :
    (descentWord hU F hF p t label hp).map' j (j + 1) =
      descentLocalValue hU F hF (label ⟨j, hj⟩)
        (p.subpath (t ⟨j, by lia⟩) (t ⟨j + 1, by lia⟩)) (hp ⟨j, hj⟩) :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ j hj

private noncomputable def descentWordValue {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentObj hU F hF (p (t 0)) ⟶ descentObj hU F hF (p (t (Fin.last n))) :=
  (descentWord hU F hF p t label hp).hom

private theorem descentWordValue_eq {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentWordValue hU F hF p t label hp =
      (descentWord hU F hF p t label hp).hom := rfl

private theorem descentWordValue_zero (t : Fin 1 → unitInterval) (label : Fin 0 → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentWordValue hU F hF p t label hp = 𝟙 (descentObj hU F hF (p (t 0))) :=
  (descentWord hU F hF p t label hp).map'_self 0

private theorem descentWordValue_one (t : Fin 2 → unitInterval) (label : Fin 1 → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentWordValue hU F hF p t label hp =
      descentLocalValue hU F hF (label 0) (p.subpath (t 0) (t 1)) (hp 0) :=
  descentWord_map_succ hU F hF p t label hp 0 (Nat.zero_lt_succ 0)

private theorem descentWordValue_split {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (k : ℕ) (hk : k ≤ n) :
    descentWordValue hU F hF p t label hp =
      (descentWord hU F hF p t label hp).map' 0 k ≫
        (descentWord hU F hF p t label hp).map' k n :=
  (descentWord hU F hF p t label hp).map'_comp 0 k n (Nat.zero_le k) hk le_rfl

-- Restricting to a consecutive chunk is the existing restriction of composable arrows.
private theorem descentWord_chunk {n k l : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (h : k + l ≤ n) :
    descentWord hU F hF p
        (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
        (fun j : Fin l => label ⟨k + j, by lia⟩)
        (fun j => hp ⟨k + j, by lia⟩) =
      (ComposableArrows.natAddLEFunctor h).obj (descentWord hU F hF p t label hp) := by
  have hobj (j : Fin (l + 1)) :
      (descentWord hU F hF p
        (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
        (fun j : Fin l => label ⟨k + j, by lia⟩)
        (fun j => hp ⟨k + j, by lia⟩)).obj j =
      ((ComposableArrows.natAddLEFunctor h).obj
        (descentWord hU F hF p t label hp)).obj j := by
    exact (descentWord_obj hU F hF p _ _ _ j).trans
      ((ComposableArrows.natAddLEFunctor_obj' h (descentWord hU F hF p t label hp)
        (i := j) (by lia)).trans
          (descentWord_obj hU F hF p t label hp ⟨k + j, by lia⟩)).symm
  apply ComposableArrows.ext
    (F := descentWord hU F hF p
      (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
      (fun j : Fin l => label ⟨k + j, by lia⟩)
      (fun j => hp ⟨k + j, by lia⟩))
    (G := (ComposableArrows.natAddLEFunctor h).obj (descentWord hU F hF p t label hp))
    hobj
  intro i hi
  apply (conj_eqToHom_iff_heq
    ((descentWord hU F hF p
      (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
      (fun j : Fin l => label ⟨k + j, by lia⟩)
      (fun j => hp ⟨k + j, by lia⟩)).map' i (i + 1))
    (((ComposableArrows.natAddLEFunctor h).obj
      (descentWord hU F hF p t label hp)).map' i (i + 1))
    (hobj ⟨i, by lia⟩) (hobj ⟨i + 1, by lia⟩)).2
  change HEq
    ((descentWord hU F hF p
      (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
      (fun j : Fin l => label ⟨k + j, by lia⟩)
      (fun j => hp ⟨k + j, by lia⟩)).map' i (i + 1))
    ((descentWord hU F hF p t label hp).map' (k + i) (k + (i + 1)))
  have hedge :
      (descentWord hU F hF p t label hp).map' (k + i) (k + (i + 1)) =
        descentLocalValue hU F hF (label ⟨k + i, by lia⟩)
          (p.subpath (t ⟨k + i, by lia⟩) (t ⟨k + (i + 1), by lia⟩))
          (hp ⟨k + i, by lia⟩) := by
    change (descentWord hU F hF p t label hp).map' (k + i) ((k + i) + 1) = _
    exact descentWord_map_succ hU F hF p t label hp (k + i) (by lia)
  exact (heq_of_eq (descentWord_map_succ hU F hF p
    (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
    (fun j : Fin l => label ⟨k + j, by lia⟩)
    (fun j => hp ⟨k + j, by lia⟩) i hi)).trans (heq_of_eq hedge).symm

private theorem descentWordValue_chunk {n k l : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (h : k + l ≤ n) :
    descentWordValue hU F hF p
        (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
        (fun j : Fin l => label ⟨k + j, by lia⟩)
        (fun j => hp ⟨k + j, by lia⟩) =
      (descentWord hU F hF p t label hp).map' k (k + l) := by
  have hmap : HEq
      (descentWordValue hU F hF p
        (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
        (fun j : Fin l => label ⟨k + j, by lia⟩)
        (fun j => hp ⟨k + j, by lia⟩))
      (((ComposableArrows.natAddLEFunctor h).obj
        (descentWord hU F hF p t label hp)).hom) :=
    CategoryTheory.Functor.hcongr_hom
      (descentWord_chunk hU F hF p t label hp h)
      (homOfLE (show (0 : Fin (l + 1)) ≤ Fin.last l from Fin.zero_le _))
  change @HEq
    (descentObj hU F hF (p (t ⟨k + 0, by lia⟩)) ⟶
      descentObj hU F hF (p (t ⟨k + l, by lia⟩)))
    (descentWordValue hU F hF p
      (fun j : Fin (l + 1) => t ⟨k + j, by lia⟩)
      (fun j : Fin l => label ⟨k + j, by lia⟩)
      (fun j => hp ⟨k + j, by lia⟩))
    (descentObj hU F hF (p (t ⟨k + 0, by lia⟩)) ⟶
      descentObj hU F hF (p (t ⟨k + l, by lia⟩)))
    ((descentWord hU F hF p t label hp).map' (k + 0) (k + l)) at hmap
  exact eq_of_heq hmap

private theorem descentWordValue_succ {n : ℕ} (t : Fin (n + 2) → unitInterval)
    (label : Fin (n + 1) → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentWordValue hU F hF p t label hp =
      descentWordValue hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc)
          (fun j : Fin n => by
            simpa only [Function.comp_apply, Fin.castSucc_succ] using hp j.castSucc) ≫
        descentLocalValue hU F hF (label (Fin.last n))
          (p.subpath (t (Fin.last n).castSucc) (t (Fin.last n).succ)) (hp (Fin.last n)) := by
  let hp' : ∀ j : Fin n,
      Set.range (p.subpath ((t ∘ Fin.castSucc) j.castSucc)
        ((t ∘ Fin.castSucc) j.succ)) ⊆ U ((label ∘ Fin.castSucc) j) :=
    fun j => by
      simpa only [Function.comp_apply, Fin.castSucc_succ] using hp j.castSucc
  have hobj (j : Fin (n + 1)) :
      (descentWord hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp').obj j =
      (descentWord hU F hF p t label hp).δlast.obj j := by
    exact (descentWord_obj hU F hF p _ _ _ j).trans
      (descentWord_obj hU F hF p t label hp j.castSucc).symm
  have hword :
      descentWord hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp' =
      (descentWord hU F hF p t label hp).δlast := by
    apply ComposableArrows.ext
      (F := descentWord hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp')
      (G := (descentWord hU F hF p t label hp).δlast) hobj
    intro j hj
    apply (conj_eqToHom_iff_heq
      ((descentWord hU F hF p
        (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp').map' j (j + 1))
      ((descentWord hU F hF p t label hp).δlast.map' j (j + 1))
      (hobj ⟨j, by lia⟩) (hobj ⟨j + 1, by lia⟩)).2
    change HEq
      ((descentWord hU F hF p
        (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp').map' j (j + 1))
      ((descentWord hU F hF p t label hp).map' j (j + 1))
    simp only [descentWord_map_succ, Function.comp_apply]; rfl
  have hmap : HEq
      (descentWordValue hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp')
      ((descentWord hU F hF p t label hp).δlast.hom) :=
    CategoryTheory.Functor.hcongr_hom hword
      (homOfLE (show (0 : Fin (n + 1)) ≤ Fin.last n from Fin.zero_le _))
  change HEq
    (descentWordValue hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp')
    ((descentWord hU F hF p t label hp).map' 0 n) at hmap
  have hprefix : (descentWord hU F hF p t label hp).map' 0 n =
      descentWordValue hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp' :=
    (eq_of_heq hmap).symm
  have hlast :
      (descentWord hU F hF p t label hp).map' n (n + 1) =
        descentLocalValue hU F hF (label (Fin.last n))
          (p.subpath (t (Fin.last n).castSucc) (t (Fin.last n).succ))
          (hp (Fin.last n)) := by
    change (descentWord hU F hF p t label hp).map' n (n + 1) =
      descentLocalValue hU F hF (label ⟨n, Nat.lt_succ_self n⟩)
        (p.subpath (t ⟨n, by lia⟩) (t ⟨n + 1, by lia⟩))
        (hp ⟨n, Nat.lt_succ_self n⟩)
    exact descentWord_map_succ hU F hF p t label hp n (Nat.lt_succ_self n)
  have hcomp :
      (descentWord hU F hF p t label hp).map' 0 n ≫
          (descentWord hU F hF p t label hp).map' n (n + 1) =
        descentWordValue hU F hF p (t ∘ Fin.castSucc) (label ∘ Fin.castSucc) hp' ≫
          descentLocalValue hU F hF (label (Fin.last n))
            (p.subpath (t (Fin.last n).castSucc) (t (Fin.last n).succ))
            (hp (Fin.last n)) :=
    congrArg₂
      (fun (f : descentObj hU F hF (p (t 0)) ⟶
          descentObj hU F hF (p (t (Fin.last n).castSucc)))
        (g : descentObj hU F hF (p (t (Fin.last n).castSucc)) ⟶
          descentObj hU F hF (p (t (Fin.last n).succ))) => f ≫ g)
      hprefix hlast
  exact (descentWordValue_split hU F hF p t label hp n (Nat.le_succ n)).trans hcomp

-- Restricting a word to its canonical prefix preserves its composite heterogeneously.
private theorem descentWordValue_prefix {n k : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (hk : k ≤ n) :
    HEq (descentWordValue hU F hF p
        (fun j : Fin (k + 1) => t (j.castLE (Nat.succ_le_succ hk)))
        (fun j : Fin k => label (j.castLE hk))
        (fun j : Fin k => hp (j.castLE hk)))
      ((descentWord hU F hF p t label hp).map' 0 k (Nat.zero_le k) hk) := by
  let W : ComposableArrows D n := descentWord hU F hF p t label hp
  have hobj (j : Fin (n + 1)) :
      descentObj hU F hF (p (t j)) = W.obj j :=
    (descentWord_obj hU F hF p t label hp j).symm
  revert hk
  induction k with
  | zero =>
    intro hk
    have hz := descentWordValue_zero hU F hF p
      (fun j : Fin 1 => t (j.castLE (Nat.succ_le_succ hk)))
      (fun j : Fin 0 => label (j.castLE hk))
      (fun j : Fin 0 => hp (j.castLE hk))
    have hid := (eqToHom_heq_id_dom _ _ (hobj 0)).symm.trans
      (eqToHom_heq_id_cod _ _ (hobj 0))
    exact (heq_of_eq hz).trans
      (hid.trans (heq_of_eq (W.map'_self 0 (Nat.zero_le n))).symm)
  | succ k ih =>
    intro hk
    have hkn : k ≤ n := (Nat.le_succ k).trans hk
    have hs := descentWordValue_succ hU F hF p
      (fun j : Fin (k + 2) => t (j.castLE (Nat.succ_le_succ hk)))
      (fun j : Fin (k + 1) => label (j.castLE hk))
      (fun j : Fin (k + 1) => hp (j.castLE hk))
    have hlast := (heq_of_eq (descentWord_map_succ hU F hF p t label hp
      k ((Nat.lt_succ_self k).trans_le hk))).symm
    have hcomp := CategoryTheory.heq_comp
      (hobj 0) (hobj ⟨k, Nat.lt_succ_of_le hkn⟩)
      (hobj ⟨k + 1, Nat.lt_succ_of_le hk⟩) (ih hkn) hlast
    exact (heq_of_eq hs).trans
      (hcomp.trans (heq_of_eq (W.map'_comp 0 k (k + 1)
        (Nat.zero_le k) (Nat.le_succ k) hk)).symm)

end WordEvaluation

private theorem descentLocalPath_refl {a : X} {s : Set X}
    (hp : Set.range (Path.refl a) ⊆ s) :
    descentLocalPath (Path.refl a) hp =
      Path.refl (⟨a, hp (Path.refl a).source_mem_range⟩ : s) := by
  apply Path.ext
  funext t
  rfl

private theorem descentLocalPath_trans {a b c : X} (p : Path a b) (q : Path b c)
    {s : Set X} (hp : Set.range p ⊆ s) (hq : Set.range q ⊆ s)
    (hpq : Set.range (p.trans q) ⊆ s) :
    descentLocalPath (p.trans q) hpq =
      (descentLocalPath p hp).trans (descentLocalPath q hq) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change ((descentLocalPath (p.trans q) hpq).map continuous_subtype_val) t =
    (((descentLocalPath p hp).trans (descentLocalPath q hq)).map
      continuous_subtype_val) t
  rw [descentLocalPath_map_subtypeVal, Path.map_trans,
    descentLocalPath_map_subtypeVal, descentLocalPath_map_subtypeVal]

private theorem descentLocalValue_refl (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) (a : X) (hp : Set.range (Path.refl a) ⊆ U i) :
    descentLocalValue hU F hF i (Path.refl a) hp = 𝟙 (descentObj hU F hF a) := by
  rw [descentLocalValue_eq, descentLocalPath_refl, fromPath_mk_refl,
    CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

private theorem descentLocalValue_trans (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b c : X} (p : Path a b) (q : Path b c)
    (hp : Set.range p ⊆ U i) (hq : Set.range q ⊆ U i)
    (hpq : Set.range (p.trans q) ⊆ U i) :
    descentLocalValue hU F hF i (p.trans q) hpq =
      descentLocalValue hU F hF i p hp ≫ descentLocalValue hU F hF i q hq := by
  rw [descentLocalValue_eq, descentLocalValue_eq, descentLocalValue_eq,
    descentLocalPath_trans p q hp hq hpq, fromPath_mk_trans, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

private theorem descentSubpath_range_subset {i : ι} {x y : X} (p : Path x y)
    {a b : unitInterval} (hab : a ≤ b)
    (hs : Set.Icc a b ⊆ p ⁻¹' (U i : Set X)) :
    Set.range (p.subpath a b) ⊆ U i := by
  rw [Path.range_subpath_of_le p a b hab]
  rintro _ ⟨t, ht, rfl⟩
  exact hs ht

section LocalValueCells

open scoped unitInterval

private theorem descentChartPath_range (i : ι) {a b : U i} (p : Path a b) :
    Set.range (p.map continuous_subtype_val) ⊆ U i := by
  rintro _ ⟨t, rfl⟩
  exact (p t).property

private theorem descentLocalValue_map_subtypeVal (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : U i} (p : Path a b)
    (hp : Set.range (p.map continuous_subtype_val) ⊆ U i) :
    descentLocalValue hU F hF i (p.map continuous_subtype_val) hp =
      eqToHom (descentObj_eq hU F hF i a.1 a.2) ≫
        (F i).map (fromPath (Path.Homotopic.Quotient.mk p)) ≫
          eqToHom (descentObj_eq hU F hF i b.1 b.2).symm := by
  have hlift : descentLocalPath (p.map continuous_subtype_val) hp = p := by
    apply Path.ext
    funext t
    apply Subtype.ext
    rfl
  rw [descentLocalValue_eq, hlift]

-- Conjugating a chart square uses only equality of its four object values.
private theorem descentLocalValue_commSq (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) (K : C(I × I, U i)) :
    CommSq
      (descentLocalValue hU F hF i
        ((Path.id.map (K.curry 0).continuous).map continuous_subtype_val)
        (descentChartPath_range i _))
      (descentLocalValue hU F hF i
        (((cellHomotopy K).evalAt 0).map continuous_subtype_val)
        (descentChartPath_range i _))
      (descentLocalValue hU F hF i
        (((cellHomotopy K).evalAt 1).map continuous_subtype_val)
        (descentChartPath_range i _))
      (descentLocalValue hU F hF i
        ((Path.id.map (K.curry 1).continuous).map continuous_subtype_val)
        (descentChartPath_range i _)) := by
  have hconj {A B C E A' B' C' E' : D}
      (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ E) (k : C ⟶ E)
      (eA : A' = A) (eB : B' = B) (eC : C' = C) (eE : E' = E)
      (hs : f ≫ h = g ≫ k) :
      (eqToHom eA ≫ f ≫ eqToHom eB.symm) ≫
          (eqToHom eB ≫ h ≫ eqToHom eE.symm) =
        (eqToHom eA ≫ g ≫ eqToHom eC.symm) ≫
          (eqToHom eC ≫ k ≫ eqToHom eE.symm) := by
    cases eA
    cases eB
    cases eC
    cases eE
    simpa only [_root_.CategoryTheory.eqToHom_refl,
      _root_.CategoryTheory.Category.id_comp,
      _root_.CategoryTheory.Category.comp_id] using hs
  refine ⟨?_⟩
  simp only [descentLocalValue_map_subtypeVal]
  simpa only [ContinuousMap.curry_apply] using
    hconj
      ((F i).map (fromPath (Path.Homotopic.Quotient.mk
        (Path.id.map (K.curry 0).continuous))))
      ((F i).map (fromPath (Path.Homotopic.Quotient.mk ((cellHomotopy K).evalAt 0))))
      ((F i).map (fromPath (Path.Homotopic.Quotient.mk ((cellHomotopy K).evalAt 1))))
      ((F i).map (fromPath (Path.Homotopic.Quotient.mk
        (Path.id.map (K.curry 1).continuous))))
      (descentObj_eq hU F hF i (K (0, 0) : X) (K (0, 0)).property)
      (descentObj_eq hU F hF i (K (0, 1) : X) (K (0, 1)).property)
      (descentObj_eq hU F hF i (K (1, 0) : X) (K (1, 0)).property)
      (descentObj_eq hU F hF i (K (1, 1) : X) (K (1, 1)).property)
      (cell_commSq K (F i)).w

-- Transport the entire square, including its implicit vertices, to new endpoints.
private theorem descentLocalValue_commSq_congr (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b c d a' b' c' d' : X}
    {p : Path a b} {q : Path a c} {r : Path b d} {s : Path c d}
    {hp : Set.range p ⊆ U i} {hq : Set.range q ⊆ U i}
    {hr : Set.range r ⊆ U i} {hs : Set.range s ⊆ U i}
    {p' : Path a' b'} {q' : Path a' c'} {r' : Path b' d'} {s' : Path c' d'}
    {hp' : Set.range p' ⊆ U i} {hq' : Set.range q' ⊆ U i}
    {hr' : Set.range r' ⊆ U i} {hs' : Set.range s' ⊆ U i}
    (ha : a' = a) (hb : b' = b) (hc : c' = c) (hd : d' = d)
    (hpc : p.cast ha hb = p') (hqc : q.cast ha hc = q')
    (hrc : r.cast hb hd = r') (hsc : s.cast hc hd = s')
    (h : CommSq (descentLocalValue hU F hF i p hp)
      (descentLocalValue hU F hF i q hq) (descentLocalValue hU F hF i r hr)
      (descentLocalValue hU F hF i s hs)) :
    CommSq (descentLocalValue hU F hF i p' hp')
      (descentLocalValue hU F hF i q' hq') (descentLocalValue hU F hF i r' hr')
      (descentLocalValue hU F hF i s' hs') := by
  subst a' b' c' d'
  simp only [Path.cast_rfl_rfl] at hpc hqc hrc hsc
  subst p' q' r' s'
  exact h

private def descentRowPath (H : C(I × I, X)) (a : I) :
    Path (H (a, 0)) (H (a, 1)) :=
  Path.id.map (H.curry a).continuous

private def descentColumnPath (H : C(I × I, X)) (c : I) :
    Path (H (0, c)) (H (1, c)) :=
  Path.id.map ((H.comp ContinuousMap.prodSwap).curry c).continuous

private theorem descentRowPath_subpath_range (H : C(I × I, X)) (i : ι)
    {a b c d : I} (hcd : c ≤ d)
    (hsmall : Set.Icc a b ×ˢ Set.Icc c d ⊆ H ⁻¹' (U i : Set X))
    (r : I) (hr : r ∈ Set.Icc a b) :
    Set.range ((descentRowPath H r).subpath c d) ⊆ U i := by
  apply descentSubpath_range_subset _ hcd
  intro s hs
  exact hsmall ⟨hr, hs⟩

private theorem descentColumnPath_subpath_range (H : C(I × I, X)) (i : ι)
    {a b c d : I} (hab : a ≤ b)
    (hsmall : Set.Icc a b ×ˢ Set.Icc c d ⊆ H ⁻¹' (U i : Set X))
    (s : I) (hs : s ∈ Set.Icc c d) :
    Set.range ((descentColumnPath H s).subpath a b) ⊆ U i := by
  apply descentSubpath_range_subset _ hab
  intro r hr
  exact hsmall ⟨hr, hs⟩

-- The vertices are the canonical ambient object values, also for zero-width cells.
private theorem descentLocalValue_rectangle_commSq (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (H : C(I × I, X)) (i : ι) (a b c d : I) (hab : a ≤ b) (hcd : c ≤ d)
    (hsmall : Set.Icc a b ×ˢ Set.Icc c d ⊆ H ⁻¹' (U i : Set X)) :
    CommSq
      (descentLocalValue hU F hF i ((descentRowPath H a).subpath c d)
        (descentRowPath_subpath_range H i hcd hsmall a ⟨le_rfl, hab⟩))
      (descentLocalValue hU F hF i ((descentColumnPath H c).subpath a b)
        (descentColumnPath_subpath_range H i hab hsmall c ⟨le_rfl, hcd⟩))
      (descentLocalValue hU F hF i ((descentColumnPath H d).subpath a b)
        (descentColumnPath_subpath_range H i hab hsmall d ⟨hcd, le_rfl⟩))
      (descentLocalValue hU F hF i ((descentRowPath H b).subpath c d)
        (descentRowPath_subpath_range H i hcd hsmall b ⟨hab, le_rfl⟩)) := by
  let K := affineCell H i a b c d hab hcd hsmall
  have h00 : H (a, c) = (K (0, 0) : X) := by
    simpa only [Set.Icc.convexComb_zero] using
      (affineCell_zero_left H i a b c d hab hcd hsmall 0).symm
  have h01 : H (a, d) = (K (0, 1) : X) := by
    simpa only [Set.Icc.convexComb_one] using
      (affineCell_zero_left H i a b c d hab hcd hsmall 1).symm
  have h10 : H (b, c) = (K (1, 0) : X) := by
    simpa only [Set.Icc.convexComb_zero] using
      (affineCell_one_left H i a b c d hab hcd hsmall 0).symm
  have h11 : H (b, d) = (K (1, 1) : X) := by
    simpa only [Set.Icc.convexComb_one] using
      (affineCell_one_left H i a b c d hab hcd hsmall 1).symm
  have hbottom :
      ((Path.id.map (K.curry 0).continuous).map continuous_subtype_val).cast h00 h01 =
        (descentRowPath H a).subpath c d := by
    apply Path.ext
    funext t
    exact affineCell_zero_left H i a b c d hab hcd hsmall t
  have hleft :
      (((cellHomotopy K).evalAt 0).map continuous_subtype_val).cast h00 h10 =
        (descentColumnPath H c).subpath a b := by
    apply Path.ext
    funext t
    exact affineCell_zero_right H i a b c d hab hcd hsmall t
  have hright :
      (((cellHomotopy K).evalAt 1).map continuous_subtype_val).cast h01 h11 =
        (descentColumnPath H d).subpath a b := by
    apply Path.ext
    funext t
    exact affineCell_one_right H i a b c d hab hcd hsmall t
  have htop :
      ((Path.id.map (K.curry 1).continuous).map continuous_subtype_val).cast h10 h11 =
        (descentRowPath H b).subpath c d := by
    apply Path.ext
    funext t
    exact affineCell_one_left H i a b c d hab hcd hsmall t
  exact descentLocalValue_commSq_congr hU F hF i h00 h01 h10 h11
    hbottom hleft hright htop (descentLocalValue_commSq hU F hF i K)

end LocalValueCells

section RowPasting

open scoped unitInterval

variable (hU : IsOpenCover U)
  (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
  (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
    (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
  (H : C(I × I, X)) (a b : I) (hab : a ≤ b)
  {n : ℕ} (t : Fin (n + 2) → I) (hmono : Monotone t) (label : Fin (n + 1) → ι)
  (hsmall : ∀ j : Fin (n + 1), Set.Icc a b ×ˢ Set.Icc (t j.castSucc) (t j.succ) ⊆
    H ⁻¹' (U (label j) : Set X))

private theorem descentRowWord_range (H : C(I × I, X)) (a b : I)
    {n : ℕ} (t : Fin (n + 2) → I) (hmono : Monotone t) (label : Fin (n + 1) → ι)
    (hsmall : ∀ j : Fin (n + 1), Set.Icc a b ×ˢ Set.Icc (t j.castSucc) (t j.succ) ⊆
      H ⁻¹' (U (label j) : Set X))
    (r : I) (hr : r ∈ Set.Icc a b) :
    ∀ j : Fin (n + 1), Set.range ((descentRowPath H r).subpath (t j.castSucc) (t j.succ)) ⊆
      U (label j) :=
  fun j => descentRowPath_subpath_range H (label j)
    (hmono (le_of_lt j.castSucc_lt_succ)) (hsmall j) r hr

-- Each node uses the cell to its right, except the final node uses the final cell.
private noncomputable def descentRowApp (j : Fin (n + 2)) :
    descentObj hU F hF (H (a, t j)) ⟶ descentObj hU F hF (H (b, t j)) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · exact descentLocalValue hU F hF (label (Fin.last n))
      ((descentColumnPath H (t (Fin.last (n + 1)))).subpath a b)
      (descentColumnPath_subpath_range H (label (Fin.last n)) hab
        (hsmall (Fin.last n)) (t (Fin.last (n + 1)))
        ⟨hmono (le_of_lt (Fin.last n).castSucc_lt_succ), le_rfl⟩)
  · exact descentLocalValue hU F hF (label k)
      ((descentColumnPath H (t k.castSucc)).subpath a b)
      (descentColumnPath_subpath_range H (label k) hab (hsmall k) (t k.castSucc)
        ⟨le_rfl, hmono (le_of_lt k.castSucc_lt_succ)⟩)

private theorem descentRowApp_eq (j : Fin (n + 2)) (i : ι)
    (hp : Set.range ((descentColumnPath H (t j)).subpath a b) ⊆ U i) :
    descentRowApp hU F hF H a b hab t hmono label hsmall j =
      descentLocalValue hU F hF i ((descentColumnPath H (t j)).subpath a b) hp := by
  revert hp
  refine Fin.lastCases ?_ (fun k => ?_) j <;> intro hp
  · simp only [descentRowApp, Fin.lastCases_last]
    exact descentLocalValue_label_independent hU F hF _ i _ _ hp
  · simp only [descentRowApp, Fin.lastCases_castSucc]
    exact descentLocalValue_label_independent hU F hF _ i _ _ hp

-- The constructor supplies all non-adjacent naturality from the cell squares.
private noncomputable def descentRowNatTrans :
    descentWord hU F hF (descentRowPath H a) t label
        (descentRowWord_range H a b t hmono label hsmall a ⟨le_rfl, hab⟩) ⟶
      descentWord hU F hF (descentRowPath H b) t label
        (descentRowWord_range H a b t hmono label hsmall b ⟨hab, le_rfl⟩) := by
  refine ComposableArrows.homMk (fun j => ?_) ?_
  · change descentObj hU F hF (H (a, t j)) ⟶ descentObj hU F hF (H (b, t j))
    exact descentRowApp hU F hF H a b hab t hmono label hsmall j
  · intro j hj
    change (descentWord hU F hF (descentRowPath H a) t label
        (descentRowWord_range H a b t hmono label hsmall a ⟨le_rfl, hab⟩)).map'
          j (j + 1) ≫
        descentRowApp hU F hF H a b hab t hmono label hsmall ⟨j + 1, by lia⟩ =
      descentRowApp hU F hF H a b hab t hmono label hsmall ⟨j, by lia⟩ ≫
        (descentWord hU F hF (descentRowPath H b) t label
          (descentRowWord_range H a b t hmono label hsmall b ⟨hab, le_rfl⟩)).map'
            j (j + 1)
    rw [descentWord_map_succ hU F hF (descentRowPath H a) t label
        (descentRowWord_range H a b t hmono label hsmall a ⟨le_rfl, hab⟩) j hj,
      descentWord_map_succ hU F hF (descentRowPath H b) t label
        (descentRowWord_range H a b t hmono label hsmall b ⟨hab, le_rfl⟩) j hj]
    let k : Fin (n + 1) := ⟨j, hj⟩
    have ht := hmono (le_of_lt k.castSucc_lt_succ)
    have hl := descentRowApp_eq hU F hF H a b hab t hmono label hsmall
      k.castSucc (label k)
      (descentColumnPath_subpath_range H (label k) hab (hsmall k) (t k.castSucc)
        ⟨le_rfl, ht⟩)
    have hr := descentRowApp_eq hU F hF H a b hab t hmono label hsmall
      k.succ (label k)
      (descentColumnPath_subpath_range H (label k) hab (hsmall k) (t k.succ)
        ⟨ht, le_rfl⟩)
    change descentLocalValue hU F hF (label k)
        ((descentRowPath H a).subpath (t k.castSucc) (t k.succ)) _ ≫
        descentRowApp hU F hF H a b hab t hmono label hsmall k.succ =
      descentRowApp hU F hF H a b hab t hmono label hsmall k.castSucc ≫
        descentLocalValue hU F hF (label k)
          ((descentRowPath H b).subpath (t k.castSucc) (t k.succ)) _
    rw [hr, hl]
    exact (descentLocalValue_rectangle_commSq hU F hF H (label k) a b
      (t k.castSucc) (t k.succ) hab ht (hsmall k)).w

private theorem descentRowNatTrans_app (j : Fin (n + 2)) :
    (descentRowNatTrans hU F hF H a b hab t hmono label hsmall).app j =
      descentRowApp hU F hF H a b hab t hmono label hsmall j := by
  rfl

private theorem descentWordValue_row :
    descentWordValue hU F hF (descentRowPath H a) t label
        (descentRowWord_range H a b t hmono label hsmall a ⟨le_rfl, hab⟩) ≫
      descentLocalValue hU F hF (label (Fin.last n))
        ((descentColumnPath H (t (Fin.last (n + 1)))).subpath a b)
        (descentColumnPath_subpath_range H (label (Fin.last n)) hab
          (hsmall (Fin.last n)) (t (Fin.last (n + 1)))
          ⟨hmono (le_of_lt (Fin.last n).castSucc_lt_succ), le_rfl⟩) =
      descentLocalValue hU F hF (label 0)
        ((descentColumnPath H (t 0)).subpath a b)
        (descentColumnPath_subpath_range H (label 0) hab (hsmall 0) (t 0)
          ⟨le_rfl, hmono (le_of_lt (0 : Fin (n + 1)).castSucc_lt_succ)⟩) ≫
        descentWordValue hU F hF (descentRowPath H b) t label
          (descentRowWord_range H a b t hmono label hsmall b ⟨hab, le_rfl⟩) := by
  have hw := ComposableArrows.naturality'
    (descentRowNatTrans hU F hF H a b hab t hmono label hsmall)
    0 (n + 1) (Nat.zero_le (n + 1)) le_rfl
  change descentWordValue hU F hF (descentRowPath H a) t label
        (descentRowWord_range H a b t hmono label hsmall a ⟨le_rfl, hab⟩) ≫
      (descentRowNatTrans hU F hF H a b hab t hmono label hsmall).app
        (Fin.last (n + 1)) =
    (descentRowNatTrans hU F hF H a b hab t hmono label hsmall).app 0 ≫
      descentWordValue hU F hF (descentRowPath H b) t label
        (descentRowWord_range H a b t hmono label hsmall b ⟨hab, le_rfl⟩) at hw
  rw [descentRowNatTrans_app hU F hF H a b hab t hmono label hsmall
      (Fin.last (n + 1)),
    descentRowNatTrans_app hU F hF H a b hab t hmono label hsmall 0] at hw
  rw [descentRowApp_eq hU F hF H a b hab t hmono label hsmall
      (Fin.last (n + 1)) (label (Fin.last n))
      (descentColumnPath_subpath_range H (label (Fin.last n)) hab
        (hsmall (Fin.last n)) (t (Fin.last (n + 1)))
        ⟨hmono (le_of_lt (Fin.last n).castSucc_lt_succ), le_rfl⟩),
    descentRowApp_eq hU F hF H a b hab t hmono label hsmall 0 (label 0)
      (descentColumnPath_subpath_range H (label 0) hab (hsmall 0) (t 0)
        ⟨le_rfl, hmono (le_of_lt (0 : Fin (n + 1)).castSucc_lt_succ)⟩)] at hw
  exact hw

end RowPasting

-- Thinness is used only in the convex parameter interval, not in the chart or ambient space.
private theorem descentLocalValue_subpath_cut (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {x y : X} (p : Path x y) (a c b : unitInterval)
    (hac : a ≤ c) (hcb : c ≤ b)
    (hs : Set.Icc a b ⊆ p ⁻¹' (U i : Set X)) :
    descentLocalValue hU F hF i (p.subpath a c)
        (descentSubpath_range_subset p hac (fun _ ht => hs ⟨ht.1, ht.2.trans hcb⟩)) ≫
      descentLocalValue hU F hF i (p.subpath c b)
        (descentSubpath_range_subset p hcb (fun _ ht => hs ⟨hac.trans ht.1, ht.2⟩)) =
      descentLocalValue hU F hF i (p.subpath a b)
        (descentSubpath_range_subset p (hac.trans hcb) hs) := by
  have hpac : Set.range (p.subpath a c) ⊆ U i :=
    descentSubpath_range_subset p hac (fun _ ht => hs ⟨ht.1, ht.2.trans hcb⟩)
  have hpcb : Set.range (p.subpath c b) ⊆ U i :=
    descentSubpath_range_subset p hcb (fun _ ht => hs ⟨hac.trans ht.1, ht.2⟩)
  have hpab : Set.range (p.subpath a b) ⊆ U i :=
    descentSubpath_range_subset p (hac.trans hcb) hs
  let K := Set.Icc (a : ℝ) (b : ℝ)
  let : ContractibleSpace K :=
    (convex_Icc (a : ℝ) (b : ℝ)).contractibleSpace
      ⟨(a : ℝ), le_rfl, hac.trans hcb⟩
  let e : C(K, unitInterval) :=
    ⟨fun t => ⟨t.1, a.2.1.trans t.2.1, t.2.2.trans b.2.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let g : C(K, U i) :=
    ⟨fun t => ⟨p (e t), hs (show e t ∈ Set.Icc a b from t.2)⟩,
      (p.continuous.comp e.continuous).subtype_mk _⟩
  let q (r s : K) : Path r s :=
    descentLocalPath (Path.segment (r : ℝ) (s : ℝ)) (by
      rw [Path.range_segment]
      exact (convex_Icc (a : ℝ) (b : ℝ)).segment_subset r.2 s.2)
  have hqmap (r s : unitInterval) (hr : a ≤ r ∧ r ≤ b) (hs' : a ≤ s ∧ s ≤ b)
      (hp : Set.range (p.subpath r s) ⊆ U i) :
      (q ⟨(r : ℝ), hr⟩ ⟨(s : ℝ), hs'⟩).map g.continuous =
        descentLocalPath (p.subpath r s) hp := by
    apply Path.ext
    funext t
    apply Subtype.ext
    apply congrArg p
    apply Subtype.ext
    exact AffineMap.lineMap_apply_ring _ _ _
  let ka : K := ⟨(a : ℝ), le_rfl, hac.trans hcb⟩
  let kc : K := ⟨(c : ℝ), hac, hcb⟩
  let kb : K := ⟨(b : ℝ), hac.trans hcb, le_rfl⟩
  have hthin :
      (fromPath (Path.Homotopic.Quotient.mk (q ka kc)) ≫
        fromPath (Path.Homotopic.Quotient.mk (q kc kb)) : mk ka ⟶ mk kb) =
      fromPath (Path.Homotopic.Quotient.mk (q ka kb)) := by
    rw [← fromPath_mk_trans]
    exact (fromPath_eq_iff_homotopic _ _).2
      (SimplyConnectedSpace.paths_homotopic ((q ka kc).trans (q kc kb)) (q ka kb))
  have hvalues :
      (F i).map (fromPath (Path.Homotopic.Quotient.mk
          (descentLocalPath (p.subpath a c) hpac))) ≫
        (F i).map (fromPath (Path.Homotopic.Quotient.mk
          (descentLocalPath (p.subpath c b) hpcb))) =
      (F i).map (fromPath (Path.Homotopic.Quotient.mk
        (descentLocalPath (p.subpath a b) hpab))) := by
    have hg := congrArg (fun f : mk ka ⟶ mk kb => (map g ⋙ F i).map f) hthin
    change (F i).map ((map g).map
        (fromPath (Path.Homotopic.Quotient.mk (q ka kc)) ≫
          fromPath (Path.Homotopic.Quotient.mk (q kc kb)))) =
      (F i).map ((map g).map (fromPath (Path.Homotopic.Quotient.mk (q ka kb)))) at hg
    rw [CategoryTheory.Functor.map_comp (map g),
      CategoryTheory.Functor.map_comp (F i), map_fromPath_mk, map_fromPath_mk,
      map_fromPath_mk,
      hqmap a c ⟨le_rfl, hac.trans hcb⟩ ⟨hac, hcb⟩ hpac,
      hqmap c b ⟨hac, hcb⟩ ⟨hac.trans hcb, le_rfl⟩ hpcb,
      hqmap a b ⟨le_rfl, hac.trans hcb⟩ ⟨hac.trans hcb, le_rfl⟩ hpab] at hg
    exact hg
  have hw := congrArg
    (fun f : (F i).obj (mk (⟨p a, hpac (p.subpath a c).source_mem_range⟩ : U i)) ⟶
        (F i).obj (mk (⟨p b, hpab (p.subpath a b).target_mem_range⟩ : U i)) =>
      eqToHom (descentObj_eq hU F hF i (p a) (hs ⟨le_rfl, hac.trans hcb⟩)) ≫ f ≫
        eqToHom (descentObj_eq hU F hF i (p b) (hs ⟨hac.trans hcb, le_rfl⟩)).symm)
    hvalues
  simp only [Category.assoc] at hw
  simpa only [descentLocalValue_eq, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp] using hw

section WordRefinement

variable (hU : IsOpenCover U)
  (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
  (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
    (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
  {a b : X} (p : Path a b)

-- A word contained in one chart evaluates to that chart's single local value.
private theorem descentWordValue_of_chart {n : ℕ} (t : Fin (n + 1) → unitInterval)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j))
    (hmono : Monotone t) (i : ι)
    (hs : Set.Icc (t 0) (t (Fin.last n)) ⊆ p ⁻¹' (U i : Set X)) :
    descentWordValue hU F hF p t label hp =
      descentLocalValue hU F hF i (p.subpath (t 0) (t (Fin.last n)))
        (descentSubpath_range_subset p (hmono (Fin.zero_le _)) hs) := by
  induction n with
  | zero =>
    rw [descentWordValue_zero]
    change 𝟙 (descentObj hU F hF (p (t 0))) =
      descentLocalValue hU F hF i (p.subpath (t 0) (t 0)) _
    have hconstant (q : Path (p (t 0)) (p (t 0)))
        (hq : Set.range q ⊆ U i) (heq : q = Path.refl (p (t 0))) :
        descentLocalValue hU F hF i q hq = 𝟙 (descentObj hU F hF (p (t 0))) := by
      subst q
      exact descentLocalValue_refl hU F hF i (p (t 0)) hq
    exact (hconstant _ _ (Path.subpath_self p (t 0))).symm
  | succ n ih =>
    have hprefix : Monotone (t ∘ Fin.castSucc) :=
      hmono.comp (fun _ _ h => h)
    have hlast : t (Fin.last n).castSucc ≤ t (Fin.last n).succ :=
      hmono (le_of_lt (Fin.last n).castSucc_lt_succ)
    have hsPrefix : Set.Icc ((t ∘ Fin.castSucc) 0)
        ((t ∘ Fin.castSucc) (Fin.last n)) ⊆ p ⁻¹' (U i : Set X) :=
      fun _ ht => hs ⟨ht.1, ht.2.trans hlast⟩
    have hsLast : Set.Icc (t (Fin.last n).castSucc) (t (Fin.last n).succ) ⊆
        p ⁻¹' (U i : Set X) :=
      fun _ ht => hs ⟨(hmono (Fin.zero_le _)).trans ht.1, ht.2⟩
    rw [descentWordValue_succ, ih _ _ _ hprefix hsPrefix]
    rw [descentLocalValue_label_independent hU F hF (label (Fin.last n)) i
      (p.subpath (t (Fin.last n).castSucc) (t (Fin.last n).succ)) (hp (Fin.last n))
      (descentSubpath_range_subset p hlast hsLast)]
    exact descentLocalValue_subpath_cut hU F hF i p
      (t 0) (t (Fin.last n).castSucc) (t (Fin.last n).succ)
      (hmono (Fin.zero_le _)) hlast hs

-- Collapse an arbitrary consecutive chunk, including a chunk with no edges.
private theorem descentWord_map_of_chart {m : ℕ} (s : Fin (m + 1) → unitInterval)
    (label : Fin m → ι)
    (hp : ∀ j, Set.range (p.subpath (s j.castSucc) (s j.succ)) ⊆ U (label j))
    (hmono : Monotone s) (k l : Fin (m + 1)) (hkl : k ≤ l) (i : ι)
    (hs : Set.Icc (s k) (s l) ⊆ p ⁻¹' (U i : Set X)) :
    (descentWord hU F hF p s label hp).map (homOfLE hkl) =
      descentLocalValue hU F hF i (p.subpath (s k) (s l))
        (descentSubpath_range_subset p (hmono hkl) hs) := by
  obtain ⟨k, hk⟩ := k
  obtain ⟨l, hl⟩ := l
  obtain ⟨d, rfl⟩ := Nat.le.dest (show k ≤ l from hkl)
  have hchunk : k + d ≤ m := by lia
  have hmonoChunk : Monotone (fun j : Fin (d + 1) => s ⟨k + j, by lia⟩) := by
    intro x y hxy
    exact hmono (Nat.add_le_add_left hxy k)
  exact (descentWordValue_chunk hU F hF p s label hp (k := k) (l := d) hchunk).symm.trans
    (descentWordValue_of_chart hU F hF p
      (fun j : Fin (d + 1) => s ⟨k + j, by lia⟩)
      (fun j : Fin d => label ⟨k + j, by lia⟩)
      (fun j => hp ⟨k + j, by lia⟩) hmonoChunk i hs)

-- The coarse nodes are the composite function, so all object equalities are reflexive.
private theorem descentWord_refines {n m : ℕ} (s : Fin (m + 1) → unitInterval)
    (hmono : Monotone s) (r : Fin (n + 1) →o Fin (m + 1))
    (fineLabel : Fin m → ι)
    (hf : ∀ j, Set.range (p.subpath (s j.castSucc) (s j.succ)) ⊆ U (fineLabel j))
    (coarseLabel : Fin n → ι)
    (hc : ∀ j, Set.range (p.subpath ((s ∘ r) j.castSucc) ((s ∘ r) j.succ)) ⊆
      U (coarseLabel j)) :
    descentWord hU F hF p (s ∘ r) coarseLabel hc =
      (descentWord hU F hF p s fineLabel hf).whiskerLeft r.toFunctor := by
  have hobj (j : Fin (n + 1)) :
      (descentWord hU F hF p (s ∘ r) coarseLabel hc).obj j =
        ((descentWord hU F hF p s fineLabel hf).whiskerLeft r.toFunctor).obj j := by
    exact (descentWord_obj hU F hF p (s ∘ r) coarseLabel hc j).trans
      ((descentWord_obj hU F hF p s fineLabel hf (r j)).symm.trans
        (ComposableArrows.whiskerLeft_obj
          (descentWord hU F hF p s fineLabel hf) r.toFunctor j).symm)
  apply ComposableArrows.ext
    (F := descentWord hU F hF p (s ∘ r) coarseLabel hc)
    (G := (descentWord hU F hF p s fineLabel hf).whiskerLeft r.toFunctor) hobj
  intro j hj
  have hij : r ⟨j, by lia⟩ ≤ r ⟨j + 1, by lia⟩ :=
    r.monotone (show (⟨j, by lia⟩ : Fin (n + 1)) ≤ ⟨j + 1, by lia⟩ from by simp)
  have hs : Set.Icc (s (r ⟨j, by lia⟩)) (s (r ⟨j + 1, by lia⟩)) ⊆
      p ⁻¹' (U (coarseLabel ⟨j, hj⟩) : Set X) := by
    intro t ht
    apply hc ⟨j, hj⟩
    change p t ∈ Set.range (p.subpath (s (r ⟨j, by lia⟩)) (s (r ⟨j + 1, by lia⟩)))
    exact (Path.range_subpath_of_le p _ _ (hmono hij)).symm ▸
      (show p t ∈ p '' Set.Icc (s (r ⟨j, by lia⟩)) (s (r ⟨j + 1, by lia⟩)) from
        ⟨t, ht, rfl⟩)
  apply (conj_eqToHom_iff_heq _ _ (hobj _) (hobj _)).2
  change HEq ((descentWord hU F hF p (s ∘ r) coarseLabel hc).map' j (j + 1))
    ((descentWord hU F hF p s fineLabel hf).map (homOfLE hij))
  have hedge := (descentWord_map_succ hU F hF p (s ∘ r) coarseLabel hc j hj).trans
    (descentWord_map_of_chart hU F hF p s fineLabel hf hmono
      (r ⟨j, by lia⟩) (r ⟨j + 1, by lia⟩) hij (coarseLabel ⟨j, hj⟩) hs).symm
  exact heq_of_eq hedge

-- Endpoint preservation identifies the total composites by the canonical equality transports.
private theorem descentWordValue_refines {n m : ℕ} (s : Fin (m + 1) → unitInterval)
    (hmono : Monotone s) (r : Fin (n + 1) →o Fin (m + 1))
    (fineLabel : Fin m → ι)
    (hf : ∀ j, Set.range (p.subpath (s j.castSucc) (s j.succ)) ⊆ U (fineLabel j))
    (coarseLabel : Fin n → ι)
    (hc : ∀ j, Set.range (p.subpath ((s ∘ r) j.castSucc) ((s ∘ r) j.succ)) ⊆
      U (coarseLabel j))
    (hzero : r 0 = 0) (hlast : r (Fin.last n) = Fin.last m) :
    descentWordValue hU F hF p (s ∘ r) coarseLabel hc =
      eqToHom (congrArg (fun j => descentObj hU F hF (p (s j))) hzero) ≫
        descentWordValue hU F hF p s fineLabel hf ≫
          eqToHom (congrArg (fun j => descentObj hU F hF (p (s j))) hlast).symm := by
  have hword := CategoryTheory.Functor.congr_hom
    (descentWord_refines hU F hF p s hmono r fineLabel hf coarseLabel hc)
    (homOfLE (show (0 : Fin (n + 1)) ≤ Fin.last n from Fin.zero_le _))
  change descentWordValue hU F hF p (s ∘ r) coarseLabel hc =
    𝟙 (descentObj hU F hF (p (s (r 0)))) ≫
      (descentWord hU F hF p s fineLabel hf).map
        (homOfLE (r.monotone (Fin.zero_le (Fin.last n)))) ≫
          𝟙 (descentObj hU F hF (p (s (r (Fin.last n))))) at hword
  have hvalue : descentWordValue hU F hF p (s ∘ r) coarseLabel hc =
      (descentWord hU F hF p s fineLabel hf).map
        (homOfLE (r.monotone (Fin.zero_le (Fin.last n)))) := by
    exact hword.trans ((Category.id_comp _).trans (Category.comp_id _))
  have hend :
      (homOfLE (r.monotone (Fin.zero_le (Fin.last n))) : r 0 ⟶ r (Fin.last n)) =
        eqToHom hzero ≫ homOfLE (show (0 : Fin (m + 1)) ≤ Fin.last m from Fin.zero_le _) ≫
          eqToHom hlast.symm := Subsingleton.elim _ _
  have hmap := congrArg (fun f : r 0 ⟶ r (Fin.last n) =>
    (descentWord hU F hF p s fineLabel hf).map f) hend
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    eqToHom_map, eqToHom_map] at hmap
  change (descentWord hU F hF p s fineLabel hf).map
      (homOfLE (r.monotone (Fin.zero_le (Fin.last n)))) =
    eqToHom (congrArg (fun j => descentObj hU F hF (p (s j))) hzero) ≫
      descentWordValue hU F hF p s fineLabel hf ≫
        eqToHom (congrArg (fun j => descentObj hU F hF (p (s j))) hlast).symm at hmap
  exact hvalue.trans hmap

end WordRefinement

-- The sorted union identifies equal cuts, so the two rank maps need not be injective.
private theorem descentCuts_common_refinement {n k : ℕ}
    (t : Fin (n + 1) → unitInterval) (u : Fin (k + 1) → unitInterval)
    (ht : Monotone t) (hu : Monotone u)
    (ht₀ : t 0 = 0) (ht₁ : t (Fin.last n) = 1)
    (hu₀ : u 0 = 0) (hu₁ : u (Fin.last k) = 1) :
    ∃ (m : ℕ) (s : Fin (m + 1) → unitInterval)
      (r : Fin (n + 1) →o Fin (m + 1)) (q : Fin (k + 1) →o Fin (m + 1)),
      Monotone s ∧ s 0 = 0 ∧ s (Fin.last m) = 1 ∧
        r 0 = 0 ∧ r (Fin.last n) = Fin.last m ∧
        q 0 = 0 ∧ q (Fin.last k) = Fin.last m ∧
        (∀ j, s (r j) = t j) ∧ (∀ j, s (q j) = u j) := by
  classical
  let S := Finset.univ.image t ∪ Finset.univ.image u
  have htm (j : Fin (n + 1)) : t j ∈ S :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_image_of_mem t (Finset.mem_univ j)))
  have hum (j : Fin (k + 1)) : u j ∈ S :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem u (Finset.mem_univ j)))
  have hzero : (0 : unitInterval) ∈ S := ht₀ ▸ htm 0
  have hone : (1 : unitInterval) ∈ S := ht₁ ▸ htm (Fin.last n)
  have hS : S.Nonempty := ⟨0, hzero⟩
  let m := S.card - 1
  have hcard : S.card = m + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (Finset.card_pos.mpr hS))).symm
  let e : Fin (m + 1) ≃o S := S.orderIsoOfFin hcard
  let s : Fin (m + 1) → unitInterval := S.orderEmbOfFin hcard
  let r : Fin (n + 1) →o Fin (m + 1) :=
    { toFun := fun j => e.symm ⟨t j, htm j⟩
      monotone' := fun a b hab =>
        e.symm.monotone (show (⟨t a, htm a⟩ : S) ≤ ⟨t b, htm b⟩ from ht hab) }
  let q : Fin (k + 1) →o Fin (m + 1) :=
    { toFun := fun j => e.symm ⟨u j, hum j⟩
      monotone' := fun a b hab =>
        e.symm.monotone (show (⟨u a, hum a⟩ : S) ≤ ⟨u b, hum b⟩ from hu hab) }
  have hrt (j : Fin (n + 1)) : s (r j) = t j := by
    change ((e (e.symm ⟨t j, htm j⟩) : S) : unitInterval) = t j
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hqu (j : Fin (k + 1)) : s (q j) = u j := by
    change ((e (e.symm ⟨u j, hum j⟩) : S) : unitInterval) = u j
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hs₀ : s 0 = 0 := by
    calc
      s 0 = S.min' hS := Finset.orderEmbOfFin_zero hcard (Nat.zero_lt_succ m)
      _ = 0 := (S.min'_eq_iff hS 0).2 ⟨hzero, fun x _ => x.2.1⟩
  have hs₁ : s (Fin.last m) = 1 := by
    calc
      s (Fin.last m) = S.max' hS :=
        Finset.orderEmbOfFin_last hcard (Nat.zero_lt_succ m)
      _ = 1 := (S.max'_eq_iff hS 1).2 ⟨hone, fun x _ => x.2.2⟩
  have hinj : Function.Injective s := (S.orderEmbOfFin hcard).injective
  refine ⟨m, s, r, q, (S.orderEmbOfFin hcard).monotone, hs₀, hs₁,
    ?_, ?_, ?_, ?_, hrt, hqu⟩
  · apply hinj
    rw [hrt, ht₀, hs₀]
  · apply hinj
    rw [hrt, ht₁, hs₁]
  · apply hinj
    rw [hqu, hu₀, hs₀]
  · apply hinj
    rw [hqu, hu₁, hs₁]

-- Every fine edge is crossed by adjacent ranks; the rank map need not be monotone.
private theorem exists_adjacent_rank_bounds {n m : ℕ}
    (r : Fin (n + 1) → Fin (m + 1))
    (h₀ : r 0 = 0) (h₁ : r (Fin.last n) = Fin.last m) (j : Fin m) :
    ∃ k : Fin n, r k.castSucc ≤ j.castSucc ∧ j.succ ≤ r k.succ := by
  have hex : ∃ i : Fin (n + 1), j.castSucc < r i := by
    refine ⟨Fin.last n, ?_⟩
    rw [h₁]
    exact j.castSucc_lt_last
  have hmin := Fin.find_spec hex
  have hne : Fin.find (fun i => j.castSucc < r i) hex ≠ 0 := by
    intro hz
    rw [hz, h₀] at hmin
    exact (not_lt_of_ge j.castSucc.zero_le) hmin
  obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hne
  refine ⟨k, ?_, ?_⟩
  · exact le_of_not_gt (Fin.find_min hex (hk ▸ k.castSucc_lt_succ))
  · exact Fin.castSucc_lt_iff_succ_le.mp (hk.symm ▸ hmin)

section PathEvaluation

open scoped unitInterval

-- Take a finite prefix of Mathlib's open-cover subdivision, retaining repeated adjacent cuts.
private theorem exists_descentSubdivision (hU : IsOpenCover U) {x y : X} (p : Path x y) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I),
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
        ∃ label : Fin n → ι,
          (∀ j, Set.Icc (t j.castSucc) (t j.succ) ⊆ p ⁻¹' (U (label j) : Set X)) ∧
            ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j) := by
  classical
  have hcover := hU.comap p.toContinuousMap
  obtain ⟨s, hs₀, hmono, ⟨m, hm⟩, hsmall⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => ((U i).comap p.toContinuousMap).isOpen)
      (by rw [hcover.iSup_set_eq_univ])
  let n := m + 1
  let t : Fin (n + 1) → I := fun j => s j
  let label : Fin n → ι := fun j => Classical.choose (hsmall j)
  have ht : Monotone t := fun _ _ hjk => hmono hjk
  have hs : ∀ j, Set.Icc (t j.castSucc) (t j.succ) ⊆ p ⁻¹' (U (label j) : Set X) :=
    fun j => Classical.choose_spec (hsmall j)
  refine ⟨n, t, ht, hs₀, hm n (Nat.le_succ m), label, hs, ?_⟩
  intro j
  exact descentSubpath_range_subset p
    (ht (show j.castSucc ≤ j.succ from Nat.le_succ j.val)) (hs j)

private noncomputable def descentPathValue (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} (p : Path x y) : descentObj hU F hF x ⟶ descentObj hU F hF y := by
  classical
  let h := exists_descentSubdivision hU p
  let t := h.choose_spec.choose
  have ht := h.choose_spec.choose_spec
  let label := ht.2.2.2.choose
  have hp := ht.2.2.2.choose_spec.2
  exact eqToHom (congrArg (descentObj hU F hF)
      ((congrArg p ht.2.1).trans p.source)).symm ≫
    descentWordValue hU F hF p t label hp ≫
      eqToHom (congrArg (descentObj hU F hF) ((congrArg p ht.2.2.1).trans p.target))

-- This equation exposes the chosen subdivision together with its interval and range bounds.
private theorem descentPathValue_eq (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} (p : Path x y) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I) (_ht : Monotone t)
      (h₀ : t 0 = 0) (h₁ : t (Fin.last n) = 1) (label : Fin n → ι)
      (_hs : ∀ j, Set.Icc (t j.castSucc) (t j.succ) ⊆ p ⁻¹' (U (label j) : Set X))
      (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)),
      descentPathValue hU F hF p =
        eqToHom (congrArg (descentObj hU F hF) ((congrArg p h₀).trans p.source)).symm ≫
          descentWordValue hU F hF p t label hp ≫
            eqToHom (congrArg (descentObj hU F hF) ((congrArg p h₁).trans p.target)) := by
  classical
  let h := exists_descentSubdivision hU p
  let t := h.choose_spec.choose
  have ht := h.choose_spec.choose_spec
  let label := ht.2.2.2.choose
  have hp := ht.2.2.2.choose_spec.2
  exact ⟨h.choose, t, ht.1, ht.2.1, ht.2.2.1, label, ht.2.2.2.choose_spec.1, hp, rfl⟩

end PathEvaluation

-- Affine half-subpaths recover the factors using Mathlib's extended-concatenation formulas.
private def pathMidpoint : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem trans_leftHalf_apply {a b c : X} (p : Path a b) (q : Path b c)
    (t : unitInterval) :
    (p.trans q) (Set.Icc.convexComb 0 pathMidpoint t) = p t := by
  have hhalf : (Set.Icc.convexComb (0 : unitInterval) pathMidpoint t : ℝ) ≤ 1 / 2 :=
    Set.Icc.convexComb_le (show (0 : unitInterval) ≤ pathMidpoint from
      unitInterval.nonneg') t
  rw [← Path.extend_extends' (p.trans q) (Set.Icc.convexComb 0 pathMidpoint t),
    Path.extend_trans_of_le_half p q hhalf]
  have ht : 2 * (Set.Icc.convexComb (0 : unitInterval) pathMidpoint t : ℝ) = (t : ℝ) := by
    simp only [Set.Icc.coe_convexComb, Set.Icc.coe_zero, pathMidpoint]
    ring
  rw [ht, Path.extend_extends']

private theorem trans_rightHalf_apply {a b c : X} (p : Path a b) (q : Path b c)
    (t : unitInterval) :
    (p.trans q) (Set.Icc.convexComb pathMidpoint 1 t) = q t := by
  have hhalf : 1 / 2 ≤ (Set.Icc.convexComb pathMidpoint (1 : unitInterval) t : ℝ) :=
    Set.Icc.le_convexComb (show pathMidpoint ≤ (1 : unitInterval) from
      unitInterval.le_one') t
  rw [← Path.extend_extends' (p.trans q) (Set.Icc.convexComb pathMidpoint 1 t),
    Path.extend_trans_of_half_le p q hhalf]
  have ht : 2 * (Set.Icc.convexComb pathMidpoint (1 : unitInterval) t : ℝ) - 1 = (t : ℝ) := by
    simp only [Set.Icc.coe_convexComb, Set.Icc.coe_one, pathMidpoint]
    ring
  rw [ht, Path.extend_extends']

private theorem trans_subpath_leftHalf {a b c : X} (p : Path a b) (q : Path b c)
    (s t : unitInterval) :
    (p.trans q).subpath (Set.Icc.convexComb 0 pathMidpoint s)
        (Set.Icc.convexComb 0 pathMidpoint t) =
      (p.subpath s t).cast (trans_leftHalf_apply p q s) (trans_leftHalf_apply p q t) := by
  apply Path.ext
  funext r
  change (p.trans q) (Set.Icc.convexComb (Set.Icc.convexComb 0 pathMidpoint s)
      (Set.Icc.convexComb 0 pathMidpoint t) r) = p (Set.Icc.convexComb s t r)
  have hparam : Set.Icc.convexComb (Set.Icc.convexComb (0 : unitInterval) pathMidpoint s)
      (Set.Icc.convexComb 0 pathMidpoint t) r =
      Set.Icc.convexComb 0 pathMidpoint (Set.Icc.convexComb s t r) := by
    apply Subtype.ext
    simpa only [Set.Icc.coe_convexComb, Set.Icc.coe_zero, AffineMap.lineMap_apply_ring] using
      ((AffineMap.lineMap (0 : ℝ) (pathMidpoint : ℝ)).apply_lineMap
        (s : ℝ) (t : ℝ) (r : ℝ)).symm
  rw [hparam, trans_leftHalf_apply]

private theorem trans_subpath_rightHalf {a b c : X} (p : Path a b) (q : Path b c)
    (s t : unitInterval) :
    (p.trans q).subpath (Set.Icc.convexComb pathMidpoint 1 s)
        (Set.Icc.convexComb pathMidpoint 1 t) =
      (q.subpath s t).cast (trans_rightHalf_apply p q s) (trans_rightHalf_apply p q t) := by
  apply Path.ext
  funext r
  change (p.trans q) (Set.Icc.convexComb (Set.Icc.convexComb pathMidpoint 1 s)
      (Set.Icc.convexComb pathMidpoint 1 t) r) = q (Set.Icc.convexComb s t r)
  have hparam : Set.Icc.convexComb (Set.Icc.convexComb pathMidpoint (1 : unitInterval) s)
      (Set.Icc.convexComb pathMidpoint 1 t) r =
      Set.Icc.convexComb pathMidpoint 1 (Set.Icc.convexComb s t r) := by
    apply Subtype.ext
    simpa only [Set.Icc.coe_convexComb, Set.Icc.coe_one, AffineMap.lineMap_apply_ring] using
      ((AffineMap.lineMap (pathMidpoint : ℝ) (1 : ℝ)).apply_lineMap
        (s : ℝ) (t : ℝ) (r : ℝ)).symm
  rw [hparam, trans_rightHalf_apply]

-- Concatenate the cuts by retaining the common midpoint only once.
private theorem exists_trans_subdivision {a b c : X} (p : Path a b) (q : Path b c)
    (V : ι → Set X) {n m : ℕ}
    (t : Fin (n + 1) → unitInterval) (u : Fin (m + 1) → unitInterval)
    (ht : Monotone t) (hu : Monotone u)
    (ht₀ : t 0 = 0) (ht₁ : t (Fin.last n) = 1)
    (hu₀ : u 0 = 0) (hu₁ : u (Fin.last m) = 1)
    (lp : Fin n → ι) (lq : Fin m → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ V (lp j))
    (hq : ∀ j, Set.range (q.subpath (u j.castSucc) (u j.succ)) ⊆ V (lq j)) :
    ∃ s : Fin (n + m + 1) → unitInterval,
      Monotone s ∧ s 0 = 0 ∧ s (Fin.last (n + m)) = 1 ∧
        (∀ j : Fin (n + 1), s ⟨j.val, by omega⟩ =
          Set.Icc.convexComb 0 pathMidpoint (t j)) ∧
        (∀ j : Fin (m + 1), s ⟨n + j.val, by omega⟩ =
          Set.Icc.convexComb pathMidpoint 1 (u j)) ∧
        (∀ j : Fin (n + m),
          Set.range ((p.trans q).subpath (s j.castSucc) (s j.succ)) ⊆
            V ((Fin.append lp lq) j)) := by
  let L : Fin (n + 1) → unitInterval := fun j => Set.Icc.convexComb 0 pathMidpoint (t j)
  let R : Fin m → unitInterval := fun j => Set.Icc.convexComb pathMidpoint 1 (u j.succ)
  let s : Fin (n + m + 1) → unitInterval :=
    fun j => Fin.append L R (Fin.cast (by omega) j)
  have hleft (j : Fin (n + 1)) : s ⟨j.val, by omega⟩ =
      Set.Icc.convexComb 0 pathMidpoint (t j) := by
    change Fin.append L R (Fin.castAdd m j) = L j
    exact Fin.append_left L R j
  have htail (j : Fin m) : s ⟨(n + 1) + j.val, by omega⟩ =
      Set.Icc.convexComb pathMidpoint 1 (u j.succ) := by
    change Fin.append L R (Fin.natAdd (n + 1) j) = R j
    exact Fin.append_right L R j
  have hright (j : Fin (m + 1)) : s ⟨n + j.val, by omega⟩ =
      Set.Icc.convexComb pathMidpoint 1 (u j) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [Fin.val_zero, Nat.add_zero, Fin.val_last, ht₁, hu₀,
        Set.Icc.convexComb_one, Set.Icc.convexComb_zero] using hleft (Fin.last n)
    · have hindex : (⟨n + k.succ.val, by omega⟩ : Fin (n + m + 1)) =
          ⟨(n + 1) + k.val, by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [hindex]
      exact htail k
  have hφleft : Monotone (Set.Icc.convexComb (0 : unitInterval) pathMidpoint) := by
    intro x y hxy
    change (Set.Icc.convexComb (0 : unitInterval) pathMidpoint x : ℝ) ≤
      (Set.Icc.convexComb (0 : unitInterval) pathMidpoint y : ℝ)
    simpa only [Set.Icc.coe_convexComb, Set.Icc.coe_zero, AffineMap.lineMap_apply_ring] using
      (AffineMap.lineMap_mono (k := ℝ)
        (show (0 : ℝ) ≤ (pathMidpoint : ℝ) from pathMidpoint.2.1)
        (show (x : ℝ) ≤ (y : ℝ) from hxy))
  have hφright : Monotone (Set.Icc.convexComb pathMidpoint (1 : unitInterval)) := by
    intro x y hxy
    change (Set.Icc.convexComb pathMidpoint (1 : unitInterval) x : ℝ) ≤
      (Set.Icc.convexComb pathMidpoint (1 : unitInterval) y : ℝ)
    simpa only [Set.Icc.coe_convexComb, Set.Icc.coe_one, AffineMap.lineMap_apply_ring] using
      (AffineMap.lineMap_mono (k := ℝ)
        (show (pathMidpoint : ℝ) ≤ 1 from pathMidpoint.2.2)
        (show (x : ℝ) ≤ (y : ℝ) from hxy))
  have hleftStart (j : Fin n) : s (Fin.castAdd m j).castSucc =
      Set.Icc.convexComb 0 pathMidpoint (t j.castSucc) := by
    calc
      s (Fin.castAdd m j).castSucc = s ⟨j.castSucc.val, by omega⟩ :=
        congrArg s (Fin.ext rfl)
      _ = _ := hleft j.castSucc
  have hleftEnd (j : Fin n) : s (Fin.castAdd m j).succ =
      Set.Icc.convexComb 0 pathMidpoint (t j.succ) := by
    calc
      s (Fin.castAdd m j).succ = s ⟨j.succ.val, by omega⟩ :=
        congrArg s (Fin.ext rfl)
      _ = _ := hleft j.succ
  have hrightStart (j : Fin m) : s (Fin.natAdd n j).castSucc =
      Set.Icc.convexComb pathMidpoint 1 (u j.castSucc) := by
    calc
      s (Fin.natAdd n j).castSucc = s ⟨n + j.castSucc.val, by omega⟩ :=
        congrArg s (Fin.ext rfl)
      _ = _ := hright j.castSucc
  have hrightEnd (j : Fin m) : s (Fin.natAdd n j).succ =
      Set.Icc.convexComb pathMidpoint 1 (u j.succ) := by
    calc
      s (Fin.natAdd n j).succ = s ⟨n + j.succ.val, by omega⟩ := by
        apply congrArg s
        apply Fin.ext
        change n + j.val + 1 = n + (j.val + 1)
        exact Nat.add_assoc _ _ _
      _ = _ := hright j.succ
  have hmono : Monotone s := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin m => ?_) j
    · calc
        s (Fin.castAdd m j).castSucc = _ := hleftStart j
        _ ≤ _ := hφleft (ht (le_of_lt j.castSucc_lt_succ))
        _ = s (Fin.castAdd m j).succ := (hleftEnd j).symm
    · calc
        s (Fin.natAdd n j).castSucc = _ := hrightStart j
        _ ≤ _ := hφright (hu (le_of_lt j.castSucc_lt_succ))
        _ = s (Fin.natAdd n j).succ := (hrightEnd j).symm
  refine ⟨s, hmono, ?_, ?_, hleft, hright, ?_⟩
  · calc
      s 0 = s ⟨(0 : Fin (n + 1)).val, by omega⟩ :=
        congrArg s (Fin.ext (by simp only [Fin.val_zero]))
      _ = Set.Icc.convexComb 0 pathMidpoint (t 0) := hleft 0
      _ = 0 := by rw [ht₀, Set.Icc.convexComb_zero]
  · calc
      s (Fin.last (n + m)) = s ⟨n + (Fin.last m).val, by omega⟩ :=
        congrArg s (Fin.ext (by simp only [Fin.val_last]))
      _ = Set.Icc.convexComb pathMidpoint 1 (u (Fin.last m)) := hright (Fin.last m)
      _ = 1 := by rw [hu₁, Set.Icc.convexComb_one]
  · intro j
    refine Fin.addCases (fun j : Fin n => ?_) (fun j : Fin m => ?_) j
    · have hcuts :
          Set.range ((p.trans q).subpath (s (Fin.castAdd m j).castSucc)
            (s (Fin.castAdd m j).succ)) =
          Set.range ((p.trans q).subpath
            (Set.Icc.convexComb 0 pathMidpoint (t j.castSucc))
            (Set.Icc.convexComb 0 pathMidpoint (t j.succ))) :=
        congrArg₂ (fun a b : unitInterval => Set.range ((p.trans q).subpath a b))
          (hleftStart j) (hleftEnd j)
      have hhalf :
          Set.range ((p.trans q).subpath
            (Set.Icc.convexComb 0 pathMidpoint (t j.castSucc))
            (Set.Icc.convexComb 0 pathMidpoint (t j.succ))) =
          Set.range (p.subpath (t j.castSucc) (t j.succ)) := by
        simpa only [Path.cast_coe] using
          congrArg (fun z : Path _ _ => Set.range z)
            (trans_subpath_leftHalf p q (t j.castSucc) (t j.succ))
      exact (congrArg₂ (fun S T : Set X => S ⊆ T)
        (hcuts.trans hhalf) (congrArg V (Fin.append_left lp lq j))).mpr (hp j)
    · have hcuts :
          Set.range ((p.trans q).subpath (s (Fin.natAdd n j).castSucc)
            (s (Fin.natAdd n j).succ)) =
          Set.range ((p.trans q).subpath
            (Set.Icc.convexComb pathMidpoint 1 (u j.castSucc))
            (Set.Icc.convexComb pathMidpoint 1 (u j.succ))) :=
        congrArg₂ (fun a b : unitInterval => Set.range ((p.trans q).subpath a b))
          (hrightStart j) (hrightEnd j)
      have hhalf :
          Set.range ((p.trans q).subpath
            (Set.Icc.convexComb pathMidpoint 1 (u j.castSucc))
            (Set.Icc.convexComb pathMidpoint 1 (u j.succ))) =
          Set.range (q.subpath (u j.castSucc) (u j.succ)) := by
        simpa only [Path.cast_coe] using
          congrArg (fun z : Path _ _ => Set.range z)
            (trans_subpath_rightHalf p q (u j.castSucc) (u j.succ))
      exact (congrArg₂ (fun S T : Set X => S ⊆ T)
        (hcuts.trans hhalf) (congrArg V (Fin.append_right lp lq j))).mpr (hq j)

-- Path endpoint casts preserve the same local path value, up to object equality transport.
private theorem descentLocalValue_cast (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b a' b' : X} (p : Path a b) (ha : a' = a) (hb : b' = b)
    (hp : Set.range p ⊆ U i) :
    descentLocalValue hU F hF i (p.cast ha hb) hp =
      eqToHom (congrArg (descentObj hU F hF) ha) ≫
        descentLocalValue hU F hF i p hp ≫
          eqToHom (congrArg (descentObj hU F hF) hb).symm := by
  subst a' b'
  simp only [Path.cast_rfl_rfl, eqToHom_refl, Category.id_comp, Category.comp_id]

-- Pointwise constancy supplies the endpoint equality even when it is not definitional.
private theorem descentLocalValue_of_constant (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : X} (p : Path a b) (hconst : ∀ t, p t = a)
    (hp : Set.range p ⊆ U i) :
    descentLocalValue hU F hF i p hp =
      eqToHom (congrArg (descentObj hU F hF) ((hconst 1).symm.trans p.target)) := by
  have hab : a = b := (hconst 1).symm.trans p.target
  subst b
  have hp' : p = Path.refl a := by
    apply Path.ext
    funext t
    exact hconst t
  subst p
  simpa only [eqToHom_refl] using descentLocalValue_refl hU F hF i a hp

section SubdivisionIndependence

open scoped unitInterval

-- A fine edge inherits a chart from an adjacent pair of coarse ranks crossing it.
private theorem exists_descentRefinementLabel {x y : X} (p : Path x y) {n m : ℕ}
    (s : Fin (m + 1) → I) (hmono : Monotone s)
    (r : Fin (n + 1) →o Fin (m + 1))
    (hzero : r 0 = 0) (hlast : r (Fin.last n) = Fin.last m)
    (coarseLabel : Fin n → ι)
    (hc : ∀ j, Set.range (p.subpath ((s ∘ r) j.castSucc) ((s ∘ r) j.succ)) ⊆
      U (coarseLabel j)) :
    ∃ fineLabel : Fin m → ι,
      ∀ j, Set.range (p.subpath (s j.castSucc) (s j.succ)) ⊆ U (fineLabel j) := by
  classical
  have hex (j : Fin m) :
      ∃ i : ι, Set.range (p.subpath (s j.castSucc) (s j.succ)) ⊆ U i := by
    obtain ⟨k, hk₀, hk₁⟩ := exists_adjacent_rank_bounds r hzero hlast j
    refine ⟨coarseLabel k, ?_⟩
    apply descentSubpath_range_subset p (hmono (le_of_lt j.castSucc_lt_succ))
    intro t ht
    apply hc k
    have hinterval : t ∈ Set.Icc ((s ∘ r) k.castSucc) ((s ∘ r) k.succ) := by
      change t ∈ Set.Icc (s (r k.castSucc)) (s (r k.succ))
      exact Set.Icc_subset_Icc (hmono hk₀) (hmono hk₁) ht
    have hmem : p t ∈ p '' Set.Icc ((s ∘ r) k.castSucc) ((s ∘ r) k.succ) :=
      ⟨t, hinterval, rfl⟩
    exact (Path.range_subpath_of_le p ((s ∘ r) k.castSucc) ((s ∘ r) k.succ)
      ((hmono.comp r.monotone) (le_of_lt k.castSucc_lt_succ))).symm ▸ hmem
  exact ⟨fun j => (hex j).choose, fun j => (hex j).choose_spec⟩

-- Endpoint normalization makes the comparison independent of the endpoint ranks.
private theorem descentWordValue_refines_normalized (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} (p : Path x y) {n m : ℕ}
    (t : Fin (n + 1) → I) (h₀ : t 0 = 0) (h₁ : t (Fin.last n) = 1)
    (s : Fin (m + 1) → I) (hmono : Monotone s)
    (hs₀ : s 0 = 0) (hs₁ : s (Fin.last m) = 1)
    (r : Fin (n + 1) →o Fin (m + 1))
    (hzero : r 0 = 0) (hlast : r (Fin.last n) = Fin.last m)
    (hcuts : ∀ j, s (r j) = t j)
    (fineLabel : Fin m → ι)
    (hf : ∀ j, Set.range (p.subpath (s j.castSucc) (s j.succ)) ⊆ U (fineLabel j))
    (coarseLabel : Fin n → ι)
    (hc : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (coarseLabel j)) :
    eqToHom (congrArg (descentObj hU F hF) ((congrArg p h₀).trans p.source)).symm ≫
        descentWordValue hU F hF p t coarseLabel hc ≫
          eqToHom (congrArg (descentObj hU F hF) ((congrArg p h₁).trans p.target)) =
      eqToHom (congrArg (descentObj hU F hF) ((congrArg p hs₀).trans p.source)).symm ≫
        descentWordValue hU F hF p s fineLabel hf ≫
          eqToHom (congrArg (descentObj hU F hF) ((congrArg p hs₁).trans p.target)) := by
  have hcuts' : t = s ∘ r := (funext hcuts).symm
  subst t
  rw [descentWordValue_refines hU F hF p s hmono r fineLabel hf coarseLabel hc
    hzero hlast]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

-- Any monotone chart-small subdivision computes the chosen global path value.
private theorem descentPathValue_eq_of_subdivision (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} (p : Path x y) {n : ℕ} (t : Fin (n + 1) → I)
    (ht : Monotone t) (h₀ : t 0 = 0) (h₁ : t (Fin.last n) = 1)
    (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentPathValue hU F hF p =
      eqToHom (congrArg (descentObj hU F hF) ((congrArg p h₀).trans p.source)).symm ≫
        descentWordValue hU F hF p t label hp ≫
          eqToHom (congrArg (descentObj hU F hF) ((congrArg p h₁).trans p.target)) := by
  classical
  obtain ⟨k, u, hu, hu₀, hu₁, chosenLabel, _hs, hc, hvalue⟩ :=
    descentPathValue_eq hU F hF p
  obtain ⟨m, s, r, q, hmono, hs₀, hs₁, hr₀, hr₁, hq₀, hq₁, hr, hq⟩ :=
    descentCuts_common_refinement u t hu ht hu₀ hu₁ h₀ h₁
  have hur : u = s ∘ (r : Fin (k + 1) → Fin (m + 1)) := by
    funext j
    exact (hr j).symm
  have hc' : ∀ j, Set.range (p.subpath ((s ∘ r) j.castSucc) ((s ∘ r) j.succ)) ⊆
      U (chosenLabel j) :=
    (congrArg (fun v : Fin (k + 1) → I =>
      ∀ j : Fin k, Set.range (p.subpath (v j.castSucc) (v j.succ)) ⊆
        U (chosenLabel j)) hur).mp hc
  obtain ⟨fineLabel, hf⟩ :=
    exists_descentRefinementLabel p s hmono r hr₀ hr₁ chosenLabel hc'
  exact hvalue.trans
    ((descentWordValue_refines_normalized hU F hF p u hu₀ hu₁ s hmono hs₀ hs₁
      r hr₀ hr₁ hr fineLabel hf chosenLabel hc).trans
      (descentWordValue_refines_normalized hU F hF p t h₀ h₁ s hmono hs₀ hs₁
        q hq₀ hq₁ hq fineLabel hf label hp).symm)

end SubdivisionIndependence

-- Take a finite prefix of Mathlib's square subdivision, retaining degenerate cells.
private theorem exists_descentGrid (hU : IsOpenCover U)
    (H : C(unitInterval × unitInterval, X)) :
    ∃ (n : ℕ) (t : Fin (n + 2) → unitInterval),
      Monotone t ∧ t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
        ∃ label : Fin (n + 1) → Fin (n + 1) → ι,
          ∀ i j, Set.Icc (t i.castSucc) (t i.succ) ×ˢ
            Set.Icc (t j.castSucc) (t j.succ) ⊆ H ⁻¹' (U (label i j) : Set X) := by
  classical
  have hcover := hU.comap H
  obtain ⟨s, hs₀, hmono, ⟨m, hm⟩, hsmall⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => ((U i).comap H).isOpen)
      (by rw [hcover.iSup_set_eq_univ])
  let t : Fin (m + 2) → unitInterval := fun j => s j
  let label : Fin (m + 1) → Fin (m + 1) → ι :=
    fun i j => Classical.choose (hsmall i j)
  refine ⟨m, t, (fun _ _ hij => hmono hij), hs₀,
    hm (m + 1) (Nat.le_succ m), label, ?_⟩
  intro i j
  exact Classical.choose_spec (hsmall i j)

section HomotopyRows

open scoped unitInterval

-- A word sees the cut points and subpaths, not the ambient endpoint presentation.
private theorem descentWordValue_cast (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y)
    {n : ℕ} (t : Fin (n + 1) → I) (label : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)) :
    descentWordValue hU F hF (p.cast hx hy) t label
        (fun j : Fin n =>
          (((_root_.Path.range_subpath (p.cast hx hy) (t j.castSucc) (t j.succ)).trans
            ((congrArg (fun f : I → X => f '' Set.uIcc (t j.castSucc) (t j.succ))
              (_root_.Path.cast_coe p hx hy)).trans
                (_root_.Path.range_subpath p (t j.castSucc) (t j.succ)).symm)).subset.trans
            (hp j))) =
      descentWordValue hU F hF p t label hp := by
  subst x' y'
  rfl

-- Pasting one chart-small row band gives equality after the fixed-endpoint transports.
private theorem descentPathValue_homotopy_row (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} {p q : Path x y} (H : p.Homotopy q) (a b : I) (hab : a ≤ b)
    {n : ℕ} (t : Fin (n + 2) → I) (ht : Monotone t)
    (h₀ : t 0 = 0) (h₁ : t (Fin.last (n + 1)) = 1) (label : Fin (n + 1) → ι)
    (hsmall : ∀ j : Fin (n + 1), Set.Icc a b ×ˢ Set.Icc (t j.castSucc) (t j.succ) ⊆
      H ⁻¹' (U (label j) : Set X)) :
    descentPathValue hU F hF (H.eval a) = descentPathValue hU F hF (H.eval b) := by
  have ha : a ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := Set.mem_Icc.mpr ⟨hab, le_rfl⟩
  have hp (r : I) (hr : r ∈ Set.Icc a b) :
      ∀ j : Fin (n + 1),
        Set.range ((H.eval r).subpath (t j.castSucc) (t j.succ)) ⊆ U (label j) :=
    descentRowWord_range H.toContinuousMap a b t ht label hsmall r hr
  have hcast (r : I) :
      (H.eval r).cast (H.source r) (H.target r) = descentRowPath H.toContinuousMap r := by
    apply Path.ext
    funext s
    rfl
  have hw (r : I) (hr : r ∈ Set.Icc a b) :
      descentWordValue hU F hF (H.eval r) t label (hp r hr) =
        descentWordValue hU F hF (descentRowPath H.toContinuousMap r) t label
          (descentRowWord_range H.toContinuousMap a b t ht label hsmall r hr) := by
    have hpc : ∀ j : Fin (n + 1),
        Set.range (((H.eval r).cast (H.source r) (H.target r)).subpath
          (t j.castSucc) (t j.succ)) ⊆ U (label j) := fun j =>
      (((_root_.Path.range_subpath ((H.eval r).cast (H.source r) (H.target r))
        (t j.castSucc) (t j.succ)).trans
          ((congrArg (fun f : I → X => f '' Set.uIcc (t j.castSucc) (t j.succ))
            (_root_.Path.cast_coe (H.eval r) (H.source r) (H.target r))).trans
              (_root_.Path.range_subpath (H.eval r)
                (t j.castSucc) (t j.succ)).symm)).subset.trans (hp r hr j))
    have hpaths :
        (⟨(H.eval r).cast (H.source r) (H.target r), hpc⟩ :
          {γ : Path (H (r, 0)) (H (r, 1)) // ∀ j : Fin (n + 1),
            Set.range (γ.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)}) =
        ⟨descentRowPath H.toContinuousMap r,
          descentRowWord_range H.toContinuousMap a b t ht label hsmall r hr⟩ :=
      Subtype.ext (hcast r)
    have hword :
        descentWord hU F hF ((H.eval r).cast (H.source r) (H.target r)) t label hpc =
          descentWord hU F hF (descentRowPath H.toContinuousMap r) t label
            (descentRowWord_range H.toContinuousMap a b t ht label hsmall r hr) :=
      congrArg (fun z :
        {γ : Path (H (r, 0)) (H (r, 1)) // ∀ j : Fin (n + 1),
          Set.range (γ.subpath (t j.castSucc) (t j.succ)) ⊆ U (label j)} =>
        (descentWord hU F hF z.val t label z.property : ComposableArrows D (n + 1)))
        hpaths
    have hmap : HEq
        (descentWordValue hU F hF ((H.eval r).cast (H.source r) (H.target r))
          t label hpc)
        (descentWordValue hU F hF (descentRowPath H.toContinuousMap r) t label
          (descentRowWord_range H.toContinuousMap a b t ht label hsmall r hr)) :=
      CategoryTheory.Functor.hcongr_hom hword
        (homOfLE (show (0 : Fin (n + 2)) ≤ Fin.last (n + 1) from Fin.zero_le _))
    have hc := descentWordValue_cast hU F hF (H.eval r)
      (H.source r) (H.target r) t label (hp r hr)
    exact eq_of_heq ((heq_of_eq hc.symm).trans hmap)
  let e₀ (r : I) : descentObj hU F hF (H (r, t 0)) = descentObj hU F hF x :=
    congrArg (descentObj hU F hF)
      ((congrArg (fun s : I => H (r, s)) h₀).trans (H.source r))
  let e₁ (r : I) :
      descentObj hU F hF (H (r, t (Fin.last (n + 1)))) = descentObj hU F hF y :=
    congrArg (descentObj hU F hF)
      ((congrArg (fun s : I => H (r, s)) h₁).trans (H.target r))
  have hv (r : I) (hr : r ∈ Set.Icc a b) :
      descentPathValue hU F hF (H.eval r) =
        eqToHom (e₀ r).symm ≫
          descentWordValue hU F hF (descentRowPath H.toContinuousMap r) t label
            (descentRowWord_range H.toContinuousMap a b t ht label hsmall r hr) ≫
              eqToHom (e₁ r) := by
    have hvalue := descentPathValue_eq_of_subdivision hU F hF (H.eval r)
      t ht h₀ h₁ label (hp r hr)
    rw [hw r hr] at hvalue
    exact hvalue
  have hpLeft :
      Set.range ((descentColumnPath H.toContinuousMap (t 0)).subpath a b) ⊆ U (label 0) :=
    descentColumnPath_subpath_range H.toContinuousMap (label 0) hab (hsmall 0) (t 0)
      (Set.mem_Icc.mpr ⟨le_rfl, ht (le_of_lt (0 : Fin (n + 1)).castSucc_lt_succ)⟩)
  have hpRight :
      Set.range ((descentColumnPath H.toContinuousMap (t (Fin.last (n + 1)))).subpath a b) ⊆
        U (label (Fin.last n)) :=
    descentColumnPath_subpath_range H.toContinuousMap (label (Fin.last n)) hab
      (hsmall (Fin.last n)) (t (Fin.last (n + 1)))
      (Set.mem_Icc.mpr ⟨ht (le_of_lt (Fin.last n).castSucc_lt_succ), le_rfl⟩)
  have hleft :
      descentLocalValue hU F hF (label 0)
          ((descentColumnPath H.toContinuousMap (t 0)).subpath a b) hpLeft =
        eqToHom ((e₀ a).trans (e₀ b).symm) := by
    exact descentLocalValue_of_constant hU F hF (label 0)
      ((descentColumnPath H.toContinuousMap (t 0)).subpath a b) (by
        intro s
        change H (Set.Icc.convexComb a b s, t 0) = H (a, t 0)
        simp only [h₀, Path.Homotopy.source]) hpLeft
  have hright :
      descentLocalValue hU F hF (label (Fin.last n))
          ((descentColumnPath H.toContinuousMap (t (Fin.last (n + 1)))).subpath a b)
          hpRight = eqToHom ((e₁ a).trans (e₁ b).symm) := by
    exact descentLocalValue_of_constant hU F hF (label (Fin.last n))
      ((descentColumnPath H.toContinuousMap (t (Fin.last (n + 1)))).subpath a b) (by
        intro s
        change H (Set.Icc.convexComb a b s, t (Fin.last (n + 1))) =
          H (a, t (Fin.last (n + 1)))
        simp only [h₁, Path.Homotopy.target]) hpRight
  have hrow :
      descentWordValue hU F hF (descentRowPath H.toContinuousMap a) t label
          (descentRowWord_range H.toContinuousMap a b t ht label hsmall a ha) ≫
        eqToHom ((e₁ a).trans (e₁ b).symm) =
      eqToHom ((e₀ a).trans (e₀ b).symm) ≫
        descentWordValue hU F hF (descentRowPath H.toContinuousMap b) t label
          (descentRowWord_range H.toContinuousMap a b t ht label hsmall b hb) := by
    have hcomm :
        descentWordValue hU F hF (descentRowPath H.toContinuousMap a) t label
            (descentRowWord_range H.toContinuousMap a b t ht label hsmall a ha) ≫
          descentLocalValue hU F hF (label (Fin.last n))
            ((descentColumnPath H.toContinuousMap (t (Fin.last (n + 1)))).subpath a b)
            hpRight =
        descentLocalValue hU F hF (label 0)
            ((descentColumnPath H.toContinuousMap (t 0)).subpath a b) hpLeft ≫
          descentWordValue hU F hF (descentRowPath H.toContinuousMap b) t label
            (descentRowWord_range H.toContinuousMap a b t ht label hsmall b hb) :=
      descentWordValue_row hU F hF H.toContinuousMap a b hab t ht label hsmall
    exact
      (congrArg
        (fun f : descentObj hU F hF (H (a, t (Fin.last (n + 1)))) ⟶
            descentObj hU F hF (H (b, t (Fin.last (n + 1)))) =>
          descentWordValue hU F hF (descentRowPath H.toContinuousMap a) t label
            (descentRowWord_range H.toContinuousMap a b t ht label hsmall a ha) ≫ f)
        hright).symm.trans
          (hcomm.trans
            (congrArg
              (fun f : descentObj hU F hF (H (a, t 0)) ⟶
                  descentObj hU F hF (H (b, t 0)) =>
                f ≫ descentWordValue hU F hF (descentRowPath H.toContinuousMap b) t label
                  (descentRowWord_range H.toContinuousMap a b t ht label hsmall b hb))
              hleft))
  rw [hv a ha, hv b hb]
  have hnormalize {A₀ A₁ B₀ B₁ A B : D} (f : A₀ ⟶ A₁) (g : B₀ ⟶ B₁)
      (ea : A₀ = A) (eb : B₀ = A) (ca : A₁ = B) (cb : B₁ = B)
      (h : f ≫ eqToHom (ca.trans cb.symm) = eqToHom (ea.trans eb.symm) ≫ g) :
      eqToHom ea.symm ≫ f ≫ eqToHom ca = eqToHom eb.symm ≫ g ≫ eqToHom cb := by
    cases ea
    cases eb
    cases ca
    cases cb
    simpa only [_root_.CategoryTheory.eqToHom_refl,
      _root_.CategoryTheory.Category.id_comp,
      _root_.CategoryTheory.Category.comp_id] using h
  exact hnormalize
    (descentWordValue hU F hF (descentRowPath H.toContinuousMap a) t label
      (descentRowWord_range H.toContinuousMap a b t ht label hsmall a ha))
    (descentWordValue hU F hF (descentRowPath H.toContinuousMap b) t label
      (descentRowWord_range H.toContinuousMap a b t ht label hsmall b hb))
    (e₀ a) (e₀ b) (e₁ a) (e₁ b) hrow

end HomotopyRows

-- Pointwise node and edge comparisons transport the composite of a finite word.
private theorem descentWordValue_congr (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {a b c d : X} (p : Path a b) (q : Path c d) {n : ℕ}
    (t u : Fin (n + 1) → unitInterval) (lp lq : Fin n → ι)
    (hp : ∀ j, Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (lp j))
    (hq : ∀ j, Set.range (q.subpath (u j.castSucc) (u j.succ)) ⊆ U (lq j))
    (hpoint : ∀ j, p (t j) = q (u j))
    (hedge : ∀ j : Fin n, p.subpath (t j.castSucc) (t j.succ) =
      (q.subpath (u j.castSucc) (u j.succ)).cast
        (hpoint j.castSucc) (hpoint j.succ)) :
    descentWordValue hU F hF p t lp hp =
      eqToHom (congrArg (descentObj hU F hF) (hpoint 0)) ≫
        descentWordValue hU F hF q u lq hq ≫
          eqToHom (congrArg (descentObj hU F hF) (hpoint (Fin.last n))).symm := by
  have hobj (j : Fin (n + 1)) :
      (descentWord hU F hF p t lp hp).obj j =
        (descentWord hU F hF q u lq hq).obj j :=
    (descentWord_obj hU F hF p t lp hp j).trans
      ((congrArg (descentObj hU F hF) (hpoint j)).trans
        (descentWord_obj hU F hF q u lq hq j).symm)
  have hq' (j : Fin n) :
      Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U (lq j) := by
    rw [hedge j]
    exact hq j
  have hword : descentWord hU F hF p t lp hp =
      descentWord hU F hF q u lq hq := by
    apply ComposableArrows.ext
      (F := descentWord hU F hF p t lp hp)
      (G := descentWord hU F hF q u lq hq) hobj
    intro i hi
    change (descentWord hU F hF p t lp hp).map' i (i + 1) =
      eqToHom (show descentObj hU F hF (p (t ⟨i, by omega⟩)) =
        descentObj hU F hF (q (u ⟨i, by omega⟩)) from
          congrArg (descentObj hU F hF) (hpoint ⟨i, by omega⟩)) ≫
        (descentWord hU F hF q u lq hq).map' i (i + 1) ≫
          eqToHom (show descentObj hU F hF (q (u ⟨i + 1, by omega⟩)) =
            descentObj hU F hF (p (t ⟨i + 1, by omega⟩)) from
              (congrArg (descentObj hU F hF) (hpoint ⟨i + 1, by omega⟩)).symm)
    rw [descentWord_map_succ, descentWord_map_succ]
    calc
      _ = descentLocalValue hU F hF (lq ⟨i, hi⟩)
          (p.subpath (t ⟨i, by omega⟩) (t ⟨i + 1, by omega⟩)) (hq' ⟨i, hi⟩) :=
        descentLocalValue_label_independent hU F hF (lp ⟨i, hi⟩) (lq ⟨i, hi⟩)
          (p.subpath (t ⟨i, by omega⟩) (t ⟨i + 1, by omega⟩))
          (hp ⟨i, hi⟩) (hq' ⟨i, hi⟩)
      _ = _ := by
        have hlocal := congrArg
          (fun r : {r : Path (p (t ⟨i, by omega⟩)) (p (t ⟨i + 1, by omega⟩)) //
              Set.range r ⊆ U (lq ⟨i, hi⟩)} =>
            descentLocalValue hU F hF (lq ⟨i, hi⟩) r.1 r.2)
          (show (⟨p.subpath (t ⟨i, by omega⟩) (t ⟨i + 1, by omega⟩),
              hq' ⟨i, hi⟩⟩ :
              {r : Path (p (t ⟨i, by omega⟩)) (p (t ⟨i + 1, by omega⟩)) //
                Set.range r ⊆ U (lq ⟨i, hi⟩)}) =
            ⟨(q.subpath (u ⟨i, by omega⟩) (u ⟨i + 1, by omega⟩)).cast
              (hpoint ⟨i, by omega⟩) (hpoint ⟨i + 1, by omega⟩), hq ⟨i, hi⟩⟩ from
            Subtype.ext (hedge ⟨i, hi⟩))
        exact hlocal.trans
          (descentLocalValue_cast hU F hF (lq ⟨i, hi⟩)
            (q.subpath (u ⟨i, by omega⟩) (u ⟨i + 1, by omega⟩))
            (hpoint ⟨i, by omega⟩) (hpoint ⟨i + 1, by omega⟩) (hq ⟨i, hi⟩))
  have hmap := CategoryTheory.Functor.congr_hom hword
    (homOfLE (show (0 : Fin (n + 1)) ≤ Fin.last n from Fin.zero_le _))
  change descentWordValue hU F hF p t lp hp =
    eqToHom (show descentObj hU F hF (p (t 0)) =
      descentObj hU F hF (q (u 0)) from
        congrArg (descentObj hU F hF) (hpoint 0)) ≫
      descentWordValue hU F hF q u lq hq ≫
        eqToHom (show descentObj hU F hF (q (u (Fin.last n))) =
          descentObj hU F hF (p (t (Fin.last n))) from
            (congrArg (descentObj hU F hF) (hpoint (Fin.last n))).symm) at hmap
  exact hmap

-- Concatenated half-subdivisions compute the composite of the chosen path values.
private theorem descentPathValue_trans (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {a b c : X} (p : Path a b) (q : Path b c) :
    descentPathValue hU F hF (p.trans q) =
      descentPathValue hU F hF p ≫ descentPathValue hU F hF q := by
  classical
  obtain ⟨n, t, ht, ht₀, ht₁, lp, _hsp, hp, hpvalue⟩ :=
    descentPathValue_eq hU F hF p
  obtain ⟨m, u, hu, hu₀, hu₁, lq, _hsq, hq, hqvalue⟩ :=
    descentPathValue_eq hU F hF q
  obtain ⟨s, hs, hs₀, hs₁, hleft, hright, hpq⟩ :=
    exists_trans_subdivision p q (fun i => (U i : Set X)) t u ht hu
      ht₀ ht₁ hu₀ hu₁ lp lq hp hq
  have hleftPoint (j : Fin (n + 1)) :
      (p.trans q) (s ⟨j.val, by omega⟩) = p (t j) :=
    (congrArg (p.trans q) (hleft j)).trans (trans_leftHalf_apply p q (t j))
  have hrightPoint (j : Fin (m + 1)) :
      (p.trans q) (s ⟨n + j.val, by omega⟩) = q (u j) :=
    (congrArg (p.trans q) (hright j)).trans (trans_rightHalf_apply p q (u j))
  have hleftEdge (j : Fin n) :
      (p.trans q).subpath (s ⟨j.val, by omega⟩) (s ⟨j.val + 1, by omega⟩) =
        (p.subpath (t j.castSucc) (t j.succ)).cast
          (hleftPoint j.castSucc) (hleftPoint j.succ) := by
    apply Path.ext
    funext r
    change ((p.trans q).subpath (s ⟨j.val, by omega⟩)
      (s ⟨j.val + 1, by omega⟩)) r = (p.subpath (t j.castSucc) (t j.succ)) r
    have hstart : (⟨j.val, by omega⟩ : Fin (n + m + 1)) =
        ⟨j.castSucc.val, by omega⟩ := by
      apply Fin.ext
      rfl
    have hend : (⟨j.val + 1, by omega⟩ : Fin (n + m + 1)) =
        ⟨j.succ.val, by omega⟩ := by
      apply Fin.ext
      rfl
    have hcuts := congrArg₂
      (fun v w : unitInterval => ((p.trans q).subpath v w) r)
      ((congrArg s hstart).trans (hleft j.castSucc))
      ((congrArg s hend).trans (hleft j.succ))
    have hhalf :
        ((p.trans q).subpath (Set.Icc.convexComb 0 pathMidpoint (t j.castSucc))
          (Set.Icc.convexComb 0 pathMidpoint (t j.succ))) r =
        (p.subpath (t j.castSucc) (t j.succ)) r := by
      exact congrArg (fun z : Path _ _ => z r)
        (trans_subpath_leftHalf p q (t j.castSucc) (t j.succ))
    exact hcuts.trans hhalf
  have hrightEdge (j : Fin m) :
      (p.trans q).subpath (s ⟨n + j.val, by omega⟩)
          (s ⟨n + (j.val + 1), by omega⟩) =
        (q.subpath (u j.castSucc) (u j.succ)).cast
          (hrightPoint j.castSucc) (hrightPoint j.succ) := by
    apply Path.ext
    funext r
    change ((p.trans q).subpath (s ⟨n + j.val, by omega⟩)
      (s ⟨n + (j.val + 1), by omega⟩)) r = (q.subpath (u j.castSucc) (u j.succ)) r
    have hstart : (⟨n + j.val, by omega⟩ : Fin (n + m + 1)) =
        ⟨n + j.castSucc.val, by omega⟩ := by
      apply Fin.ext
      rfl
    have hend : (⟨n + (j.val + 1), by omega⟩ : Fin (n + m + 1)) =
        ⟨n + j.succ.val, by omega⟩ := by
      apply Fin.ext
      rfl
    have hcuts := congrArg₂
      (fun v w : unitInterval => ((p.trans q).subpath v w) r)
      ((congrArg s hstart).trans (hright j.castSucc))
      ((congrArg s hend).trans (hright j.succ))
    have hhalf :
        ((p.trans q).subpath (Set.Icc.convexComb pathMidpoint 1 (u j.castSucc))
          (Set.Icc.convexComb pathMidpoint 1 (u j.succ))) r =
        (q.subpath (u j.castSucc) (u j.succ)) r := by
      exact congrArg (fun z : Path _ _ => z r)
        (trans_subpath_rightHalf p q (u j.castSucc) (u j.succ))
    exact hcuts.trans hhalf
  have hprefix :
      (descentWord hU F hF (p.trans q) s (Fin.append lp lq) hpq).map' 0 n =
        eqToHom (congrArg (descentObj hU F hF) (hleftPoint 0)) ≫
          descentWordValue hU F hF p t lp hp ≫
            eqToHom (congrArg (descentObj hU F hF) (hleftPoint (Fin.last n))).symm := by
    have hcomparison := descentWordValue_congr hU F hF (p.trans q) p
      (fun j : Fin (n + 1) => s ⟨j.val, by omega⟩) t
      (fun j : Fin n => (Fin.append lp lq) ⟨j.val, by omega⟩) lp
      (fun j : Fin n => hpq ⟨j.val, by omega⟩) hp hleftPoint hleftEdge
    let W : ComposableArrows D (n + m) :=
      descentWord hU F hF (p.trans q) s (Fin.append lp lq) hpq
    have hobj (j : Fin (n + m + 1)) :
        W.obj j = descentObj hU F hF ((p.trans q) (s j)) :=
      descentWord_obj hU F hF (p.trans q) s (Fin.append lp lq) hpq j
    let e₀ := congrArg (descentObj hU F hF) (hleftPoint 0)
    let e₁ := congrArg (descentObj hU F hF) (hleftPoint (Fin.last n))
    have hlocal := (heq_of_eq hcomparison).trans
      ((eqToHom_comp_heq
        (descentWordValue hU F hF p t lp hp ≫ eqToHom e₁.symm) e₀).trans
          (comp_eqToHom_heq (descentWordValue hU F hF p t lp hp) e₁.symm))
    have hcanonical := descentWordValue_prefix hU F hF (p.trans q)
      s (Fin.append lp lq) hpq (k := n) (by omega)
    exact (conj_eqToHom_iff_heq
      (W.map' 0 n (Nat.zero_le n) (by omega))
      (descentWordValue hU F hF p t lp hp)
      ((hobj 0).trans e₀) ((hobj ⟨n, by omega⟩).trans e₁)).2
        (hcanonical.symm.trans hlocal)
  have hsuffix :
      (descentWord hU F hF (p.trans q) s (Fin.append lp lq) hpq).map' n (n + m) =
        eqToHom (congrArg (descentObj hU F hF) (hrightPoint 0)) ≫
          descentWordValue hU F hF q u lq hq ≫
            eqToHom (congrArg (descentObj hU F hF) (hrightPoint (Fin.last m))).symm := by
    have hcomparison := descentWordValue_congr hU F hF (p.trans q) q
      (fun j : Fin (m + 1) => s ⟨n + j.val, by omega⟩) u
      (fun j : Fin m => (Fin.append lp lq) ⟨n + j.val, by omega⟩) lq
      (fun j : Fin m => hpq ⟨n + j.val, by omega⟩) hq hrightPoint hrightEdge
    exact (descentWordValue_chunk hU F hF (p.trans q)
      s (Fin.append lp lq) hpq (k := n) (l := m) (by omega)).symm.trans hcomparison
  rw [descentPathValue_eq_of_subdivision hU F hF (p.trans q)
    s hs hs₀ hs₁ (Fin.append lp lq) hpq, hpvalue, hqvalue,
    descentWordValue_split hU F hF (p.trans q) s (Fin.append lp lq) hpq n (by omega),
    hprefix, hsuffix]
  have hnormalize {A B C P₀ P₁ Q₀ Q₁ S₀ S₁ S₂ : D}
      (f : P₀ ⟶ P₁) (g : Q₀ ⟶ Q₁)
      (ha : S₀ = A) (hc : S₂ = C)
      (hl₀ : S₀ = P₀) (hl₁ : S₁ = P₁)
      (hr₀ : S₁ = Q₀) (hr₁ : S₂ = Q₁)
      (hp₀ : P₀ = A) (hp₁ : P₁ = B) (hq₀ : Q₀ = B) (hq₁ : Q₁ = C) :
      eqToHom ha.symm ≫
          ((eqToHom hl₀ ≫ f ≫ eqToHom hl₁.symm) ≫
            eqToHom hr₀ ≫ g ≫ eqToHom hr₁.symm) ≫ eqToHom hc =
        (eqToHom hp₀.symm ≫ f ≫ eqToHom hp₁) ≫
          (eqToHom hq₀.symm ≫ g ≫ eqToHom hq₁) := by
    cases hp₀
    cases hp₁
    cases hq₀
    cases hq₁
    cases hl₀
    cases hl₁
    cases hr₁
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact hnormalize (descentWordValue hU F hF p t lp hp)
    (descentWordValue hU F hF q u lq hq)
    (congrArg (descentObj hU F hF) ((congrArg (p.trans q) hs₀).trans (p.trans q).source))
    (congrArg (descentObj hU F hF) ((congrArg (p.trans q) hs₁).trans (p.trans q).target))
    (congrArg (descentObj hU F hF) (hleftPoint 0))
    (congrArg (descentObj hU F hF) (hleftPoint (Fin.last n)))
    (congrArg (descentObj hU F hF) (hrightPoint 0))
    (congrArg (descentObj hU F hF) (hrightPoint (Fin.last m)))
    (congrArg (descentObj hU F hF) ((congrArg p ht₀).trans p.source))
    (congrArg (descentObj hU F hF) ((congrArg p ht₁).trans p.target))
    (congrArg (descentObj hU F hF) ((congrArg q hu₀).trans q.source))
    (congrArg (descentObj hU F hF) ((congrArg q hu₁).trans q.target))

-- A chart-small path is computed by the subdivision with just its two endpoint cuts.
private theorem descentPathValue_eq_of_range_subset (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} (p : Path x y) (i : ι) (hp : Set.range p ⊆ U i) :
    descentPathValue hU F hF p = descentLocalValue hU F hF i p hp := by
  let t : Fin 2 → unitInterval := Fin.cases 0 (fun _ => 1)
  have ht : Monotone t := by
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    rw [Fin.eq_zero j]
    exact unitInterval.nonneg'
  have hp' : ∀ j : Fin 1,
      Set.range (p.subpath (t j.castSucc) (t j.succ)) ⊆ U i := by
    intro j
    rintro _ ⟨s, rfl⟩
    exact hp ⟨Set.Icc.convexComb (t j.castSucc) (t j.succ) s, rfl⟩
  have hlocal : ∀ hq : Set.range (p.subpath 0 1) ⊆ U i,
      descentLocalValue hU F hF i (p.subpath 0 1) hq =
        eqToHom (congrArg (descentObj hU F hF) p.source) ≫
          descentLocalValue hU F hF i p hp ≫
            eqToHom (congrArg (descentObj hU F hF) p.target).symm := by
    apply (congrArg (fun q : Path (p 0) (p 1) =>
      ∀ hq : Set.range q ⊆ U i,
        descentLocalValue hU F hF i q hq =
          eqToHom (congrArg (descentObj hU F hF) p.source) ≫
            descentLocalValue hU F hF i p hp ≫
              eqToHom (congrArg (descentObj hU F hF) p.target).symm)
      (Path.subpath_zero_one p)).mpr
    intro hq
    exact descentLocalValue_cast hU F hF i p p.source p.target hp
  have hone :
      descentWordValue hU F hF p t (fun _ => i) hp' =
        eqToHom (congrArg (descentObj hU F hF) p.source) ≫
          descentLocalValue hU F hF i p hp ≫
            eqToHom (congrArg (descentObj hU F hF) p.target).symm :=
    (descentWordValue_one hU F hF p t (fun _ => i) hp').trans (hlocal (hp' 0))
  have hnormalize {A B A' B' : D} (f : A ⟶ B) (g : A' ⟶ B')
      (ha : A = A') (hb : B = B') (h : f = eqToHom ha ≫ g ≫ eqToHom hb.symm) :
      eqToHom ha.symm ≫ f ≫ eqToHom hb = g := by
    cases ha
    cases hb
    simpa only [_root_.CategoryTheory.eqToHom_refl,
      _root_.CategoryTheory.Category.id_comp,
      _root_.CategoryTheory.Category.comp_id] using h
  exact (descentPathValue_eq_of_subdivision hU F hF p t ht rfl rfl (fun _ => i) hp').trans
    (hnormalize (descentWordValue hU F hF p t (fun _ => i) hp')
      (descentLocalValue hU F hF i p hp)
      (congrArg (descentObj hU F hF) p.source)
      (congrArg (descentObj hU F hF) p.target) hone)

private theorem descentPathValue_refl (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (x : X) :
    descentPathValue hU F hF (Path.refl x) = 𝟙 (descentObj hU F hF x) := by
  obtain ⟨i, hi⟩ := hU.exists_mem x
  have hp : Set.range (Path.refl x) ⊆ U i := by
    rintro _ ⟨_, rfl⟩
    exact hi
  exact (descentPathValue_eq_of_range_subset hU F hF (Path.refl x) i hp).trans
    (descentLocalValue_refl hU F hF i x hp)

-- Chain the chart-small rows of a fixed-endpoint homotopy.
private theorem descentPathValue_homotopic (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} {p q : Path x y} (hpq : p.Homotopic q) :
    descentPathValue hU F hF p = descentPathValue hU F hF q := by
  obtain ⟨H⟩ := hpq
  obtain ⟨n, t, ht, ht0, ht1, label, hsmall⟩ :=
    exists_descentGrid hU H.toContinuousMap
  have hstep (j : Fin (n + 1)) :
      descentPathValue hU F hF (H.eval (t j.castSucc)) =
        descentPathValue hU F hF (H.eval (t j.succ)) :=
    descentPathValue_homotopy_row hU F hF H (t j.castSucc) (t j.succ)
      (ht (Fin.castSucc_le_succ j)) t ht ht0 ht1 (label j) (hsmall j)
  have hchain (k : Fin (n + 2)) :
      descentPathValue hU F hF (H.eval (t 0)) =
        descentPathValue hU F hF (H.eval (t k)) := by
    induction k using Fin.induction with
    | zero => rfl
    | succ j ih => exact ih.trans (hstep j)
  have h := hchain (Fin.last (n + 1))
  rw [ht0, ht1, Path.Homotopy.eval_zero, Path.Homotopy.eval_one] at h
  exact h

private theorem descentPathValue_map_subtypeVal (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : U i} (p : Path a b) :
    descentPathValue hU F hF
        (p.map (ContinuousMap.subtypeVal (U i : Set X)).continuous) =
      eqToHom (descentObj_eq hU F hF i (a : X) a.property) ≫
        (F i).map (fromPath (Path.Homotopic.Quotient.mk p)) ≫
          eqToHom (descentObj_eq hU F hF i (b : X) b.property).symm := by
  exact (descentPathValue_eq_of_range_subset hU F hF
    (p.map (ContinuousMap.subtypeVal (U i : Set X)).continuous) i
    (descentChartPath_range i p)).trans
      (descentLocalValue_map_subtypeVal hU F hF i p (descentChartPath_range i p))

/-- Extend strictly compatible chart functors along an arbitrary indexed open cover.

The compatibility equations concern the two restrictions from each pairwise intersection.
This is the all-point groupoid form of May's Chapter 2, §7 argument, generalized to covers
without connectedness or intersection-closure conditions and to arbitrary target categories.
Object and morphism universes of the target are independent of the space and cover index. -/
@[no_expose]
noncomputable def descOfIsOpenCover (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j) :
    FundamentalGroupoid X ⥤ D := by
  refine
    { obj := fun x => descentObj hU F hF x.as
      map := fun {x y} p =>
        _root_.Quotient.lift (fun p : Path x.as y.as => descentPathValue hU F hF p)
          (fun _ _ hpq => descentPathValue_homotopic hU F hF hpq) p
      map_id := ?_
      map_comp := ?_ }
  · intro x
    exact descentPathValue_refl hU F hF x.as
  · intro x y z p q
    exact Path.Homotopic.Quotient.ind₂
      (fun p q => descentPathValue_trans hU F hF p q) p q

private theorem descOfIsOpenCover_obj_eq (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (x : X) :
    (descOfIsOpenCover hU F hF).obj (mk x) = descentObj hU F hF x := rfl

private theorem descOfIsOpenCover_map_mk (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    {x y : X} (p : Path x y) :
    (descOfIsOpenCover hU F hF).map (fromPath (Path.Homotopic.Quotient.mk p)) =
      descentPathValue hU F hF p := rfl

/-- Descent restricts by equality, rather than natural isomorphism, to each chart functor. -/
@[simp]
theorem inclusion_comp_descOfIsOpenCover (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j) (i : ι) :
    map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ descOfIsOpenCover hU F hF = F i := by
  have hobj (a : FundamentalGroupoid (U i)) :
      (map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ descOfIsOpenCover hU F hF).obj a =
        (F i).obj a :=
    (descOfIsOpenCover_obj_eq hU F hF (a.as : X)).trans
      (descentObj_eq hU F hF i (a.as : X) a.as.property)
  refine CategoryTheory.Functor.ext hobj ?_
  intro a b f
  apply (conj_eqToHom_iff_heq _ _ (hobj a) (hobj b)).2
  induction f using Path.Homotopic.Quotient.ind with
  | mk p =>
    -- Normalize both morphism carriers before composing the representative-path equations.
    change @HEq
      (descentObj hU F hF (a.as : X) ⟶ descentObj hU F hF (b.as : X))
      ((descOfIsOpenCover hU F hF).map
        (fromPath (Path.Homotopic.Quotient.mk (p.map continuous_subtype_val))))
      ((F i).obj (mk a.as) ⟶ (F i).obj (mk b.as))
      ((F i).map (fromPath (Path.Homotopic.Quotient.mk p)))
    have hmap : @HEq
        (descentObj hU F hF (a.as : X) ⟶ descentObj hU F hF (b.as : X))
        ((descOfIsOpenCover hU F hF).map
          (fromPath (Path.Homotopic.Quotient.mk (p.map continuous_subtype_val))))
        (descentObj hU F hF (a.as : X) ⟶ descentObj hU F hF (b.as : X))
        (descentPathValue hU F hF (p.map continuous_subtype_val)) :=
      heq_of_eq (descOfIsOpenCover_map_mk hU F hF (p.map continuous_subtype_val))
    exact hmap.trans ((conj_eqToHom_iff_heq
      (descentPathValue hU F hF (p.map continuous_subtype_val))
      ((F i).map (fromPath (Path.Homotopic.Quotient.mk p)))
      (descentObj_eq hU F hF i (a.as : X) a.as.property)
      (descentObj_eq hU F hF i (b.as : X) b.as.property)).mp
        (descentPathValue_map_subtypeVal hU F hF i p))

/-- The descended object agrees with the value in every chart containing the point. -/
theorem descOfIsOpenCover_obj (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) (x : X) (hx : x ∈ U i) :
    (descOfIsOpenCover hU F hF).obj (mk x) = (F i).obj (mk ⟨x, hx⟩) := by
  exact Functor.congr_obj (inclusion_comp_descOfIsOpenCover hU F hF i) (mk ⟨x, hx⟩)

/-- On a local path class, descent is the local map transported by its object equalities. -/
theorem descOfIsOpenCover_map (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : FundamentalGroupoid (U i)} (f : a ⟶ b) :
    (descOfIsOpenCover hU F hF).map ((map (ContinuousMap.subtypeVal (U i : Set X))).map f) =
      eqToHom (descOfIsOpenCover_obj hU F hF i a.as.1 a.as.2) ≫ (F i).map f ≫
        eqToHom (descOfIsOpenCover_obj hU F hF i b.as.1 b.as.2).symm := by
  exact Functor.congr_hom (inclusion_comp_descOfIsOpenCover hU F hF i) f

/-- The representative-path form of the local arrow equation. All endpoint transport is
through equality of object values, with no chosen isomorphisms in the target. -/
theorem descOfIsOpenCover_map_fromPath (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (i : ι) {a b : U i} (p : Path a b) :
    (descOfIsOpenCover hU F hF).map
        (fromPath (Path.Homotopic.Quotient.mk (p.map continuous_subtype_val))) =
      eqToHom (descOfIsOpenCover_obj hU F hF i a.1 a.2) ≫
        (F i).map (fromPath (Path.Homotopic.Quotient.mk p)) ≫
          eqToHom (descOfIsOpenCover_obj hU F hF i b.1 b.2).symm := by
  exact descOfIsOpenCover_map hU F hF i (fromPath (Path.Homotopic.Quotient.mk p))

/-- Equality uniqueness: the chart restrictions determine the descended functor. -/
theorem descOfIsOpenCover_unique (hU : IsOpenCover U)
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ D)
    (hF : ∀ i j, (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j)
    (K : FundamentalGroupoid X ⥤ D)
    (hK : ∀ i, map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ K = F i) :
    K = descOfIsOpenCover hU F hF := by
  have hlocal (i : ι) :
      map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ K =
        map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ descOfIsOpenCover hU F hF :=
    (hK i).trans (inclusion_comp_descOfIsOpenCover hU F hF i).symm
  have hobj (x : FundamentalGroupoid X) :
      K.obj x = (descOfIsOpenCover hU F hF).obj x := by
    obtain ⟨i, hi⟩ := hU.exists_mem x.as
    exact Functor.congr_obj (hlocal i) (mk ⟨x.as, hi⟩)
  let α : K ⟶ descOfIsOpenCover hU F hF :=
    natTransOfIsOpenCover hU (fun x => eqToHom (hobj x)) (by
      intro i x y f
      -- Equality transports agree with the global components by proof irrelevance.
      simpa only [MorphismProperty.naturalityProperty, Functor.comp_map, eqToHom_app]
        using (eqToHom (hlocal i)).naturality f)
  refine CategoryTheory.Functor.ext hobj ?_
  intro x y f
  have hnat : K.map f ≫ eqToHom (hobj y) =
      eqToHom (hobj x) ≫ (descOfIsOpenCover hU F hF).map f :=
    α.naturality f
  simpa only [Category.assoc] using
    (comp_eqToHom_iff (hobj y) (K.map f)
      (eqToHom (hobj x) ≫ (descOfIsOpenCover hU F hF).map f)).mp hnat

/-- The inclusion cocone of an arbitrary open cover is a colimit in `Grpd`.

This is the strict all-point groupoid colimit theorem of May, Chapter 2, §7, with arbitrary
indexed open covers in place of path-connected intersection-closed diagrams. -/
noncomputable def isColimitOpenCoverCocone (hU : IsOpenCover U) :
    IsColimit (openCoverCocone U) := by
  let F (s : Cocone (openCoverDiagram U)) (i : ι) :
      FundamentalGroupoid (U i) ⥤ s.pt := s.ι.app (.single i)
  have hF (s : Cocone (openCoverDiagram U)) (i j : ι) :
      (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F s i =
        (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F s j := by
    exact (s.w (Pairwise.Hom.left i j)).trans (s.w (Pairwise.Hom.right i j)).symm
  have hrestrict (s : Cocone (openCoverDiagram U)) (i : ι) :
      (openCoverCocone U).ι.app (.single i) ≫ descOfIsOpenCover hU (F s) (hF s) =
        s.ι.app (.single i) :=
    inclusion_comp_descOfIsOpenCover hU (F s) (hF s) i
  refine
    { desc := fun s => descOfIsOpenCover hU (F s) (hF s)
      fac := ?_
      uniq := ?_ }
  · intro s k
    cases k with
    | single i => exact hrestrict s i
    | pair i j =>
      let d : (openCoverCocone U).pt ⟶ s.pt := descOfIsOpenCover hU (F s) (hF s)
      have hd : (openCoverCocone U).ι.app (.single i) ≫ d = s.ι.app (.single i) :=
        hrestrict s i
      change (openCoverCocone U).ι.app (.pair i j) ≫ d = s.ι.app (.pair i j)
      calc
        (openCoverCocone U).ι.app (.pair i j) ≫ d =
            (openCoverDiagram U).map (Pairwise.Hom.left i j) ≫
              ((openCoverCocone U).ι.app (.single i) ≫ d) :=
          ((openCoverCocone U).w_assoc (Pairwise.Hom.left i j) d).symm
        _ = (openCoverDiagram U).map (Pairwise.Hom.left i j) ≫ s.ι.app (.single i) :=
          congrArg (fun f => (openCoverDiagram U).map (Pairwise.Hom.left i j) ≫ f) hd
        _ = s.ι.app (.pair i j) := s.w (Pairwise.Hom.left i j)
  · intro s m hm
    exact descOfIsOpenCover_unique hU (F s) (hF s) m (fun i => hm (.single i))

/-- The same inclusion cocone is a colimit in `Cat`, allowing arbitrary category vertices
at the fixed bundled sizes. Its `desc`, `fac` and `uniq` are those of `IsColimit`. -/
noncomputable def isColimitOpenCoverCatCocone (hU : IsOpenCover U) :
    IsColimit (openCoverCatCocone U) := by
  let F (s : Cocone (openCoverCatDiagram U)) (i : ι) :
      FundamentalGroupoid (U i) ⥤ s.pt := (s.ι.app (.single i)).toFunctor
  have hF (s : Cocone (openCoverCatDiagram U)) (i j : ι) :
      (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F s i =
        (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F s j := by
    exact congrArg Cat.Hom.toFunctor
      ((s.w (Pairwise.Hom.left i j)).trans (s.w (Pairwise.Hom.right i j)).symm)
  have hrestrict (s : Cocone (openCoverCatDiagram U)) (i : ι) :
      (openCoverCatCocone U).ι.app (.single i) ≫
          (descOfIsOpenCover hU (F s) (hF s)).toCatHom = s.ι.app (.single i) := by
    apply Cat.ext
    exact inclusion_comp_descOfIsOpenCover hU (F s) (hF s) i
  refine
    { desc := fun s => (descOfIsOpenCover hU (F s) (hF s)).toCatHom
      fac := ?_
      uniq := ?_ }
  · intro s k
    cases k with
    | single i => exact hrestrict s i
    | pair i j =>
      let d : (openCoverCatCocone U).pt ⟶ s.pt :=
        (descOfIsOpenCover hU (F s) (hF s)).toCatHom
      have hd : (openCoverCatCocone U).ι.app (.single i) ≫ d = s.ι.app (.single i) :=
        hrestrict s i
      change (openCoverCatCocone U).ι.app (.pair i j) ≫ d = s.ι.app (.pair i j)
      calc
        (openCoverCatCocone U).ι.app (.pair i j) ≫ d =
            (openCoverCatDiagram U).map (Pairwise.Hom.left i j) ≫
              ((openCoverCatCocone U).ι.app (.single i) ≫ d) :=
          ((openCoverCatCocone U).w_assoc (Pairwise.Hom.left i j) d).symm
        _ = (openCoverCatDiagram U).map (Pairwise.Hom.left i j) ≫ s.ι.app (.single i) :=
          congrArg (fun f => (openCoverCatDiagram U).map (Pairwise.Hom.left i j) ≫ f) hd
        _ = s.ι.app (.pair i j) := s.w (Pairwise.Hom.left i j)
  · intro s m hm
    apply Cat.ext
    exact descOfIsOpenCover_unique hU (F s) (hF s) m.toFunctor
      (fun i => congrArg Cat.Hom.toFunctor (hm (.single i)))

end FundamentalGroupoid
