/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageResolution
public import ContinuousGroupCohomology.ContinuousCohomologyFunctor
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import ContinuousGroupCohomology.FiniteAveraging

/-!
# Diagonal insertion for coinduced continuous cochains

The resolution is the recursively iterated compact-open space `C(G, -)`, with
the twisted coinduced action. Inserting the evaluation argument as the first
homogeneous argument defines an equivariant map between consecutive terms and
then a map on invariant cochains. No identification with continuous maps out
of a Cartesian power is used.

The pointwise alternating-sum formula for the differential proves that diagonal
insertion contracts coinduced homogeneous cochains in positive degree. The
resulting boundaries represent every positive-degree cohomology class.
The coefficient functor transports this vanishing across representation
isomorphisms.

## References

* Mathlib's `ContRepresentation.coind₁` and `TopRep.homogeneousCochains`.
* Formal Frontier's earlier diagonal-insertion formalization of the swap,
  diagonal and recursive insertion and their contraction argument for coinduced
  cochains. These constructions and proofs adapt that approach to this
  library's `TopRep` resolution and API.
-/

@[expose] public section

universe u v w

open CategoryTheory ContRepresentation TopRep

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluate an iterated coinduced resolution term, one coordinate at a time.
The tuple is only an index for successive evaluations, not a topological
identification of the resolution with a function space on a product. -/
def resolutionEval (Y : TopRep.{max v w} k G) :
    (n : ℕ) → resolutionX Y n → (Fin n → G) → Y
  | 0, f, _ => f
  | n + 1, f, hs => resolutionEval Y n (f (hs 0)) (Fin.tail hs)

@[simp] theorem resolutionEval_zero (Y : TopRep.{max v w} k G) (f : Y)
    (hs : Fin 0 → G) : resolutionEval Y 0 f hs = f := rfl

@[simp] theorem resolutionEval_succ (Y : TopRep.{max v w} k G) (n : ℕ)
    (f : resolutionX Y (n + 1)) (hs : Fin (n + 1) → G) :
    resolutionEval Y (n + 1) f hs =
      resolutionEval Y n (f (hs 0)) (Fin.tail hs) := rfl

/-- Iterated evaluation determines a term of the resolution. -/
theorem resolutionEval_ext (Y : TopRep.{max v w} k G) (n : ℕ)
    {f f' : resolutionX Y n}
    (h : ∀ hs : Fin n → G, resolutionEval Y n f hs = resolutionEval Y n f' hs) :
    f = f' := by
  induction n with
  | zero => exact h (fun j => j.elim0)
  | succ n ih =>
    ext g
    apply ih
    intro hs
    simpa only [resolutionEval_succ, Fin.cons_zero, Fin.tail_cons] using
      h (Fin.cons g hs)

/-- Iterated evaluation commutes with coefficient maps through the
recursively defined resolution. -/
theorem resolutionEval_map {Y Z : TopRep.{max v w} k G} (f : Y ⟶ Z) :
    ∀ (n : ℕ) (a : resolutionX Y n) (hs : Fin n → G),
      resolutionEval Z n
        ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n).hom a) hs =
      f.hom (resolutionEval Y n a hs)
  | 0, _, _ => rfl
  | n + 1, a, hs => resolutionEval_map f n (a (hs 0)) (Fin.tail hs)

@[simp] theorem resolutionEval_add (Y : TopRep.{max v w} k G) (n : ℕ)
    (f f' : resolutionX Y n) (hs : Fin n → G) :
    resolutionEval Y n (f + f') hs =
      resolutionEval Y n f hs + resolutionEval Y n f' hs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [resolutionEval_succ, ContinuousMap.add_apply] using
      ih (f (hs 0)) (f' (hs 0)) (Fin.tail hs)

@[simp] theorem resolutionEval_neg (Y : TopRep.{max v w} k G) (n : ℕ)
    (f : resolutionX Y n) (hs : Fin n → G) :
    resolutionEval Y n (-f) hs = -resolutionEval Y n f hs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [resolutionEval_succ, ContinuousMap.neg_apply] using
      ih (f (hs 0)) (Fin.tail hs)

@[simp] theorem resolutionEval_sub (Y : TopRep.{max v w} k G) (n : ℕ)
    (f f' : resolutionX Y n) (hs : Fin n → G) :
    resolutionEval Y n (f - f') hs =
      resolutionEval Y n f hs - resolutionEval Y n f' hs := by
  rw [sub_eq_add_neg, resolutionEval_add, resolutionEval_neg, sub_eq_add_neg]

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem removeNth_succ_cons (n : ℕ) (hs : Fin (n + 1) → G)
    (t : G) (j : Fin (n + 1)) :
    (Fin.succ j).removeNth (Fin.cons t hs : Fin (n + 2) → G) =
      (Fin.cons t (j.removeNth hs) : Fin (n + 1) → G) := by
  change (Fin.cons t hs) ∘ j.succ.succAbove = Fin.cons t (j.removeNth hs)
  exact Fin.cons_comp_succ_succAbove t hs j

/-- The differential on recursively iterated coinduced functions is the alternating
sum over deleted evaluation arguments. -/
theorem resolutionEval_d (Y : TopRep.{max v w} k G) :
    ∀ (n : ℕ) (f : resolutionX Y n) (hs : Fin (n + 1) → G),
      resolutionEval Y (n + 1) ((d Y n).hom f) hs =
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
          resolutionEval Y n f (j.removeNth hs)
  | 0, f, hs => by
    change ((d Y 0).hom f) (hs 0) =
      ∑ j : Fin 1, (-1 : ℤ) ^ j.val • f
    simp [d_zero]
  | n + 1, f, hs => by
    change resolutionEval Y (n + 1)
      (((d Y (n + 1)).hom f) (hs 0)) (Fin.tail hs) = _
    rw [hom_d_succ]
    change resolutionEval Y (n + 1)
      (f - (d Y n).hom (f (hs 0))) (Fin.tail hs) = _
    rw [resolutionEval_sub]
    have hs_eq : hs = Fin.cons (hs 0) (Fin.tail hs) :=
      (Fin.cons_self_tail hs).symm
    conv_rhs => rw [hs_eq]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.removeNth_zero, Fin.tail_cons]
    rw [resolutionEval_d Y n (f (hs 0)) (Fin.tail hs)]
    simp_rw [removeNth_succ_cons]
    simp only [resolutionEval_succ, Fin.cons_zero, Fin.tail_cons,
      Fin.val_succ, pow_succ]
    simp; abel

end TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G]

/-- Swap two successive coinduced evaluation arguments. -/
def swapCoind (Y : TopRep.{max v w} k G) [DiscreteTopology Y] :
    Y.ρ.coind₁.coind₁ →ⁱL Y.ρ.coind₁.coind₁ where
  toFun f := ContinuousMap.curry
    ⟨fun p : G × G => f p.2 p.1,
      continuous_eval.comp ((f.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  map_add' f f' := by ext g t; rfl
  map_smul' scalar f := by ext g t; rfl
  cont := by
    let : DiscreteTopology C(G, Y) := ContinuousMap.discreteTopology_of_compactSpace
    let : DiscreteTopology C(G, C(G, Y)) :=
      ContinuousMap.discreteTopology_of_compactSpace
    exact continuous_of_discreteTopology
  isIntertwining' g := by
    ext f h t
    simp [ContinuousMap.curry_apply, ContRepresentation.coind₁_apply_apply]

@[simp] theorem swapCoind_apply (Y : TopRep.{max v w} k G) [DiscreteTopology Y]
    (f : C(G, C(G, Y))) (g t : G) : swapCoind Y f g t = f t g := rfl

/-- Swapping two arguments is an involution. -/
theorem swapCoind_swapCoind (Y : TopRep.{max v w} k G) [DiscreteTopology Y] :
    (swapCoind Y).comp (swapCoind Y) = ContIntertwiningMap.id := by
  ext f g t
  rfl

/-- Evaluation of two coinduced arguments at the same group element. -/
def diagonalCoind (Y : TopRep.{max v w} k G) [DiscreteTopology Y] :
    Y.ρ.coind₁.coind₁ →ⁱL Y.ρ.coind₁ where
  toFun f :=
    ⟨fun t => f t t, continuous_eval.comp (f.continuous.prodMk continuous_id)⟩
  map_add' f f' := by ext t; rfl
  map_smul' scalar f := by ext t; rfl
  cont := by
    let : DiscreteTopology C(G, Y) := ContinuousMap.discreteTopology_of_compactSpace
    let : DiscreteTopology C(G, C(G, Y)) :=
      ContinuousMap.discreteTopology_of_compactSpace
    exact continuous_of_discreteTopology
  isIntertwining' g := by
    ext f t
    simp [ContRepresentation.coind₁_apply_apply]

@[simp] theorem diagonalCoind_apply (Y : TopRep.{max v w} k G) [DiscreteTopology Y]
    (f : C(G, C(G, Y))) (t : G) : diagonalCoind Y f t = f t t := rfl

/-- Diagonal evaluation is unchanged by swapping the arguments. -/
theorem diagonalCoind_comp_swapCoind (Y : TopRep.{max v w} k G)
    [DiscreteTopology Y] :
    (diagonalCoind Y).comp (swapCoind Y) = diagonalCoind Y := by
  ext f t
  rfl

/-- Diagonal evaluation commutes with equivariant coefficient maps. -/
theorem diagonalCoind_natural {Y Z : TopRep.{max v w} k G}
    [DiscreteTopology Y] [DiscreteTopology Z] (f : Y ⟶ Z) :
    (diagonalCoind Z).comp (coind₁Map (coind₁Map f.hom)) =
      (coind₁Map f.hom).comp (diagonalCoind Y) := by
  ext a t
  rfl

/-- Swapping arguments commutes with equivariant coefficient maps. -/
theorem swapCoind_natural {Y Z : TopRep.{max v w} k G}
    [DiscreteTopology Y] [DiscreteTopology Z] (f : Y ⟶ Z) :
    (swapCoind Z).comp (coind₁Map (coind₁Map f.hom)) =
      (coind₁Map (coind₁Map f.hom)).comp (swapCoind Y) := by
  ext a g t
  rfl

/-- Recursively insert the evaluation variable into a coinduced resolution term.
The outer argument is swapped inward until diagonal evaluation reaches the
original coinduced coefficient. -/
def insertCoind (X : TopRep.{max v w} k G) [DiscreteTopology X] : (m : ℕ) →
    (TopRep.resolutionX (TopRep.coind₁ X) (m + 2)).ρ →ⁱL
      (TopRep.resolutionX (TopRep.coind₁ X) (m + 1)).ρ
  | 0 => by
    letI : DiscreteTopology (TopRep.coind₁ X) :=
      ContinuousMap.discreteTopology_of_compactSpace
    exact (coind₁Map (diagonalCoind X)).comp (swapCoind (TopRep.coind₁ X))
  | m + 1 => by
    letI : DiscreteTopology (TopRep.coind₁ X) :=
      ContinuousMap.discreteTopology_of_compactSpace
    letI : DiscreteTopology (TopRep.resolutionX (TopRep.coind₁ X) (m + 1)) :=
      ContinuousCohomology.discreteTopology_resolutionX (TopRep.coind₁ X) (m + 1)
    exact (coind₁Map (insertCoind X m)).comp
      (swapCoind (TopRep.resolutionX (TopRep.coind₁ X) (m + 1)))

/-- The recursive insertion evaluates at `t` after inserting `t` as the first
homogeneous argument. -/
@[simp] theorem insertCoind_eval (X : TopRep.{max v w} k G)
    [DiscreteTopology X] :
    ∀ (m : ℕ) (f : TopRep.resolutionX (TopRep.coind₁ X) (m + 2))
      (hs : Fin (m + 1) → G) (t : G),
      (TopRep.resolutionEval (TopRep.coind₁ X) (m + 1)
        (insertCoind X m f) hs) t =
      (TopRep.resolutionEval (TopRep.coind₁ X) (m + 2)
        f (Fin.cons t hs)) t
  | 0, _, _, _ => rfl
  | m + 1, f, hs, t => by
    let : DiscreteTopology (TopRep.coind₁ X) :=
      ContinuousMap.discreteTopology_of_compactSpace
    let : DiscreteTopology (TopRep.resolutionX (TopRep.coind₁ X) (m + 1)) :=
      ContinuousCohomology.discreteTopology_resolutionX (TopRep.coind₁ X) (m + 1)
    exact insertCoind_eval X m
      ((swapCoind (TopRep.resolutionX (TopRep.coind₁ X) (m + 1)) f) (hs 0))
      (Fin.tail hs) t

/-- Insertion commutes pointwise with coefficient maps on the recursive
resolution. The `resolutionMap` is Mathlib's map for the identity group map. -/
theorem insertCoind_natural_apply {X Y : TopRep.{max v w} k G}
    [DiscreteTopology X] [DiscreteTopology Y] (f : X ⟶ Y) (m : ℕ)
    (a : TopRep.resolutionX (TopRep.coind₁ X) (m + 2)) :
    insertCoind Y m
        ((resolutionMap (X := TopRep.coind₁ X) (ContinuousMonoidHom.id G)
          ((coind₁Functor k G).map f) (m + 2)).hom a) =
      (resolutionMap (X := TopRep.coind₁ X) (ContinuousMonoidHom.id G)
        ((coind₁Functor k G).map f) (m + 1)).hom (insertCoind X m a) := by
  apply TopRep.resolutionEval_ext (TopRep.coind₁ Y) (m + 1)
  intro hs
  apply ContinuousMap.ext
  intro t
  rw [insertCoind_eval Y m]
  rw [TopRep.resolutionEval_map ((coind₁Functor k G).map f)]
  rw [TopRep.resolutionEval_map ((coind₁Functor k G).map f)]
  exact congrArg f.hom (insertCoind_eval X m a hs t).symm

/-- Diagonal insertion on the invariant homogeneous cochain complex. -/
def coind₁Insert (X : TopRep.{max v w} k G) [DiscreteTopology X] (m : ℕ) :
    (TopRep.homogeneousCochains (TopRep.coind₁ X)).X (m + 1) ⟶
      (TopRep.homogeneousCochains (TopRep.coind₁ X)).X m :=
  TopModuleCat.ofHom ((insertCoind X m).mapInvariants)

/-- Evaluate a cochain after insertion without unfolding the resolution. -/
@[simp] theorem coind₁Insert_apply (X : TopRep.{max v w} k G)
    [DiscreteTopology X] (m : ℕ)
    (σ : (TopRep.homogeneousCochains (TopRep.coind₁ X)).X (m + 1))
    (hs : Fin (m + 1) → G) (t : G) :
    (TopRep.resolutionEval (TopRep.coind₁ X) (m + 1)
      ((coind₁Insert X m).hom σ).1 hs) t =
    (TopRep.resolutionEval (TopRep.coind₁ X) (m + 2)
      σ.1 (Fin.cons t hs)) t :=
  insertCoind_eval X m σ.1 hs t

/-- Diagonal insertion is natural in the coefficient representation. -/
theorem coind₁Insert_natural {X Y : TopRep.{max v w} k G}
    [DiscreteTopology X] [DiscreteTopology Y] (f : X ⟶ Y) (m : ℕ) :
    coind₁Insert X m ≫
        (cochainsMap (ContinuousMonoidHom.id G)
          ((coind₁Functor k G).map f)).f m =
      (cochainsMap (ContinuousMonoidHom.id G)
        ((coind₁Functor k G).map f)).f (m + 1) ≫ coind₁Insert Y m := by
  ext σ
  apply Subtype.ext
  exact (insertCoind_natural_apply f m σ.1).symm

private theorem insert_homotopy_raw (X : TopRep.{max v w} k G)
    [DiscreteTopology X] (m : ℕ)
    (f : TopRep.resolutionX (TopRep.coind₁ X) (m + 2)) :
    (TopRep.d (TopRep.coind₁ X) (m + 1)).hom (insertCoind X m f) +
      insertCoind X (m + 1)
        ((TopRep.d (TopRep.coind₁ X) (m + 2)).hom f) = f := by
  let F := TopRep.coind₁ X
  apply TopRep.resolutionEval_ext F (m + 2)
  intro hs
  apply ContinuousMap.ext
  intro t
  have hfirst := congrArg (ContinuousMap.evalCLM k t)
    (TopRep.resolutionEval_d F (m + 1) (insertCoind X m f) hs)
  simp only [map_sum, map_zsmul, ContinuousMap.evalCLM_apply] at hfirst
  have hfirst' :
      (TopRep.resolutionEval F (m + 2)
        ((TopRep.d F (m + 1)).hom (insertCoind X m f)) hs) t =
        ∑ j : Fin (m + 2), (-1 : ℤ) ^ j.val •
          (TopRep.resolutionEval F (m + 2) f
            (Fin.cons t (j.removeNth hs))) t := by
    calc
      _ = ∑ j : Fin (m + 2), (-1 : ℤ) ^ j.val •
            (TopRep.resolutionEval F (m + 1) (insertCoind X m f)
              (j.removeNth hs)) t := hfirst
      _ = _ := Finset.sum_congr rfl (fun j _ => by
        rw [insertCoind_eval X m f (j.removeNth hs) t])
  have hsecond := insertCoind_eval X (m + 1)
    ((TopRep.d F (m + 2)).hom f) hs t
  have hthird := congrArg (ContinuousMap.evalCLM k t)
    (TopRep.resolutionEval_d F (m + 2) f (Fin.cons t hs))
  simp only [map_sum, map_zsmul, ContinuousMap.evalCLM_apply] at hthird
  have hthird' :
      (TopRep.resolutionEval F (m + 3) ((TopRep.d F (m + 2)).hom f)
        (Fin.cons t hs)) t =
        (TopRep.resolutionEval F (m + 2) f hs) t -
          ∑ j : Fin (m + 2), (-1 : ℤ) ^ j.val •
            (TopRep.resolutionEval F (m + 2) f
              (Fin.cons t (j.removeNth hs))) t := by
    rw [hthird, Fin.sum_univ_succ]
    simp only [Fin.removeNth_zero, Fin.tail_cons, TopRep.removeNth_succ_cons,
      Fin.val_succ, pow_succ]
    simp; abel
  change (TopRep.resolutionEval F (m + 2)
    ((TopRep.d F (m + 1)).hom (insertCoind X m f) +
      insertCoind X (m + 1) ((TopRep.d F (m + 2)).hom f)) hs) t =
        (TopRep.resolutionEval F (m + 2) f hs) t
  rw [TopRep.resolutionEval_add, ContinuousMap.add_apply, hfirst', hsecond, hthird']
  abel

/-- The diagonal insertion contracts the coinduced complex in positive degree. -/
theorem coind₁Insert_homotopy (X : TopRep.{max v w} k G)
    [DiscreteTopology X] (m : ℕ) :
    let C := TopRep.homogeneousCochains (TopRep.coind₁ X)
    coind₁Insert X m ≫ C.d m (m + 1) +
      C.d (m + 1) (m + 2) ≫ coind₁Insert X (m + 1) =
        𝟙 (C.X (m + 1)) := by
  dsimp only
  rw [TopRep.homogeneousCochains.d_eq, TopRep.homogeneousCochains.d_eq]
  ext σ
  apply Subtype.ext
  simpa [coind₁Insert, ContIntertwiningMap.mapInvariants_apply] using
    insert_homotopy_raw X m σ.1

/-- Continuous cohomology with coinduced discrete coefficients vanishes in
every strictly positive degree. -/
theorem coind₁_positive_eq_zero (X : TopRep.{max v w} k G)
    [DiscreteTopology X] (m : ℕ)
    (a : continuousCohomology (m + 1) (TopRep.coind₁ X)) : a = 0 := by
  let F := TopRep.coind₁ X
  let C := TopRep.homogeneousCochains F
  obtain ⟨z, rfl⟩ := π_surjective F (m + 1) a
  have hboundary : C.iCycles (m + 1) =
      (C.iCycles (m + 1) ≫ coind₁Insert X m) ≫ C.d m (m + 1) := by
    have hhomotopy : coind₁Insert X m ≫ C.d m (m + 1) +
        C.d (m + 1) (m + 2) ≫ coind₁Insert X (m + 1) =
        𝟙 (C.X (m + 1)) := coind₁Insert_homotopy X m
    have h := congrArg (fun f : C.X (m + 1) ⟶ C.X (m + 1) =>
      C.iCycles (m + 1) ≫ f) hhomotopy
    simpa only [Preadditive.comp_add, ← CategoryTheory.Category.assoc,
      C.iCycles_d, CategoryTheory.Limits.zero_comp, add_zero,
      CategoryTheory.Category.comp_id] using h.symm
  have hfactor : (C.iCycles (m + 1) ≫ coind₁Insert X m) ≫
      C.toCycles m (m + 1) = 𝟙 (C.cycles (m + 1)) := by
    apply (cancel_mono (C.iCycles (m + 1))).mp
    calc
      ((C.iCycles (m + 1) ≫ coind₁Insert X m) ≫
          C.toCycles m (m + 1)) ≫ C.iCycles (m + 1) =
          (C.iCycles (m + 1) ≫ coind₁Insert X m) ≫ C.d m (m + 1) := by
            rw [CategoryTheory.Category.assoc, C.toCycles_i]
      _ = C.iCycles (m + 1) := hboundary.symm
      _ = 𝟙 (C.cycles (m + 1)) ≫ C.iCycles (m + 1) := by simp
  have hπzero : C.homologyπ (m + 1) = 0 := by
    calc
      C.homologyπ (m + 1) =
          ((C.iCycles (m + 1) ≫ coind₁Insert X m) ≫
            C.toCycles m (m + 1)) ≫ C.homologyπ (m + 1) := by
              rw [hfactor, CategoryTheory.Category.id_comp]
      _ = 0 := by
        rw [CategoryTheory.Category.assoc, C.toCycles_comp_homologyπ,
          CategoryTheory.Limits.comp_zero]
  change (C.homologyπ (m + 1)).hom z = 0
  rw [hπzero]
  rfl

/-- Positive continuous cohomology vanishes for any representation isomorphic
to coinduction from a discrete representation of a compact group. -/
theorem coind₁_isomorphic_positive_eq_zero
    (X : TopRep.{max v w} k G) [DiscreteTopology X]
    {Y : TopRep.{max v w} k G} (e : Y ≅ TopRep.coind₁ X)
    (m : ℕ) (a : continuousCohomology (m + 1) Y) : a = 0 := by
  let e' := (coefficientFunctor (k := k) (G := G) (m + 1)).mapIso e
  have hz : e'.hom.hom a = 0 := coind₁_positive_eq_zero X m (e'.hom.hom a)
  apply e'.toContinuousLinearEquiv.injective
  change e'.hom.hom a = e'.hom.hom 0
  simpa only [_root_.map_zero e'.hom.hom] using hz

end ContinuousCohomology
