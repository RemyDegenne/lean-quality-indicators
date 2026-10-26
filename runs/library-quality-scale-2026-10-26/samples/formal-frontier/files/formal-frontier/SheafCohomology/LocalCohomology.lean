/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Functors

public section

/-!
# Local cohomology presheaves

For a continuous map `f : X ⟶ Y`, this file packages the existing
cohomology presheaf on `X` as a presheaf on `Y`: on an open `U ⊆ Y`, its
value is the Ext-based local cohomology group attached to `f ⁻¹ U`.
Restriction maps and functoriality in the coefficient sheaf are inherited from
`CategoryTheory.Sheaf.cohomologyPresheafFunctor`.

We also package the sheafification of this presheaf and its canonical unit.
The later `OpenCohomology` and `OpenCohomologyRightDerived` modules construct
the open-restriction comparison and its positive-degree natural right-derived
pushforward comparison in their supported common universe. No degree-zero
right-derived comparison is asserted here.

The construction has the common space/coefficient/Ext universe boundary of
the current topological cohomology-presheaf API.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [HasSheafify
  (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The presheaf on `Y` whose value on `U` is the Ext-based local cohomology
of a sheaf on `X` over `f ⁻¹ U`, functorial in the coefficient sheaf. -/
@[expose] def localCohomologyPresheafFunctor (q : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Presheaf AddCommGrpCat.{u} := by
  change CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ _
  exact CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X) q ⋙
      (Functor.whiskeringLeft _ _ _).obj (Opens.map f).op

/-- The local-cohomology presheaf of `F` along `f` in degree `q`. -/
abbrev localCohomologyPresheaf
    (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) :
    Y.Presheaf AddCommGrpCat.{u} :=
  (localCohomologyPresheafFunctor f q).obj F

@[simp]
lemma localCohomologyPresheaf_obj
    (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) (U : Opens Y) :
    (localCohomologyPresheaf f F q).obj (.op U) =
      CategoryTheory.Sheaf.H'
        (show CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} from F)
        q ((Opens.map f).obj U) := rfl

@[simp]
lemma localCohomologyPresheaf_map
    (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    {U V : Opens Y} (i : U ⟶ V) :
    (localCohomologyPresheaf f F q).map i.op =
      (CategoryTheory.Sheaf.cohomologyPresheaf
        (show CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} from F) q).map
            ((Opens.map f).map i).op := rfl

@[simp]
lemma localCohomologyPresheafFunctor_map_app
    (q : ℕ) {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G)
    (U : Opens Y) :
    ((localCohomologyPresheafFunctor f q).map a).app (.op U) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q).map a).app
          (.op ((Opens.map f).obj U)) := rfl

variable [HasSheafify
  (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]

/-- Sheafification of the local-cohomology presheaf, functorial in the
coefficient sheaf. -/
@[expose] def sheafifiedLocalCohomologyFunctor (q : ℕ) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Y.Sheaf AddCommGrpCat.{u} := by
  change CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    CategoryTheory.Sheaf
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  exact localCohomologyPresheafFunctor f q ⋙
    presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}

/-- The sheafified local cohomology of `F` along `f` in degree `q`. -/
abbrev sheafifiedLocalCohomology
    (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) :
    Y.Sheaf AddCommGrpCat.{u} :=
  (sheafifiedLocalCohomologyFunctor f q).obj F

/-- The canonical map from the local-cohomology presheaf to the underlying
presheaf of its sheafification. -/
@[expose] def toSheafifiedLocalCohomology (q : ℕ) :
    localCohomologyPresheafFunctor f q ⟶
      sheafifiedLocalCohomologyFunctor f q ⋙
        TopCat.Sheaf.forget AddCommGrpCat.{u} Y :=
  Functor.whiskerLeft (localCohomologyPresheafFunctor f q)
    (sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit

@[simp]
lemma toSheafifiedLocalCohomology_app
    (q : ℕ) (F : X.Sheaf AddCommGrpCat.{u}) :
    (toSheafifiedLocalCohomology f q).app F =
      (sheafificationAdjunction
        (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
          (localCohomologyPresheaf f F q) := rfl

end TopCat.Sheaf
