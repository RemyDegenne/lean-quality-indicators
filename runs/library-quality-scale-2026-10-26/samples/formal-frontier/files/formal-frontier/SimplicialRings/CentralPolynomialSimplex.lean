/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monomial
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.Algebra.Ring.Center
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Central polynomial simplices over arbitrary rings

The indeterminates of `CentralPolynomialSimplex.PolyRing R n` commute with the entire
coefficient ring, even when that ring is noncommutative. The coordinate with
index zero is eliminated using the relation that the homogeneous coordinates sum to one.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

/-- The ring of polynomials in `n` central indeterminates over a possibly
noncommutative unital ring. -/
abbrev PolyRing (R : Type u) [Ring R] (n : ℕ) := AddMonoidAlgebra R (Fin n →₀ ℕ)

variable {R : Type u} [Ring R]

/-- The coefficient inclusion. -/
def coefficient (n : ℕ) : R →+* PolyRing R n := AddMonoidAlgebra.singleZeroRingHom

/-- A free homogeneous coordinate, indexed starting at one. -/
def generator (n : ℕ) (j : Fin n) : PolyRing R n :=
  AddMonoidAlgebra.of' R (Fin n →₀ ℕ) (Finsupp.single j 1)

/-- Homogeneous coordinates, including the eliminated zeroth coordinate. -/
def coordinate (n : ℕ) : Fin (n + 1) → PolyRing R n :=
  Fin.cases (1 - ∑ j : Fin n, generator n j) (generator n)

@[simp] theorem coordinate_zero (n : ℕ) : coordinate (R := R) n 0 =
    1 - ∑ j : Fin n, generator (R := R) n j := rfl

@[simp] theorem coordinate_succ (n : ℕ) (j : Fin n) :
    coordinate (R := R) n j.succ = generator n j := rfl

theorem generator_mem_center (n : ℕ) (j : Fin n) :
    generator (R := R) n j ∈ Set.center (PolyRing R n) :=
  Semigroup.mem_center_iff.mpr fun p =>
    (AddMonoidAlgebra.of'_commute (R := R) (M := Fin n →₀ ℕ)
      (fun _ => add_comm _ _) p).eq.symm

theorem coordinate_mem_center (n : ℕ) (j : Fin (n + 1)) :
    coordinate (R := R) n j ∈ Set.center (PolyRing R n) := by
  refine Fin.cases ?_ (fun j => generator_mem_center n j) j
  change (1 - ∑ j : Fin n, generator (R := R) n j) ∈ Set.center (PolyRing R n)
  rw [sub_eq_add_neg]
  apply Set.add_mem_center Set.one_mem_center
  apply Set.neg_mem_center
  exact Finset.sum_induction _ _ (fun _ _ => Set.add_mem_center)
    (Semigroup.mem_center_iff.mpr (by intro; simp))
    (fun j _ => generator_mem_center n j)

/-- Map a ring with central coefficient-commuting variables into an arbitrary ring.
The `center` witness is stronger than necessary but is natural for polynomial simplices. -/
noncomputable def substitute {B : Type v} [Ring B] (n : ℕ)
    (f : R →+* B) (values : Fin n → Submonoid.center B) : PolyRing R n →+* B := by
  letI := Submonoid.center.commMonoid (M := B)
  let h : (Fin n →₀ ℕ) →+ Additive (Submonoid.center B) :=
    Finsupp.liftAddHom (fun j => multiplesHom (Additive (Submonoid.center B))
      (Additive.ofMul (values j)))
  let g : Multiplicative (Fin n →₀ ℕ) →* B :=
    { toFun := fun p => (h p.toAdd).toMul
      map_one' := by change ((h 0).toMul : B) = 1; simp
      map_mul' := by
        intro p q
        change ((h (p.toAdd + q.toAdd)).toMul : B) =
          (h p.toAdd).toMul * (h q.toAdd).toMul
        exact congrArg (fun z : Additive (Submonoid.center B) => (z.toMul : B))
          (h.map_add p.toAdd q.toAdd) }
  exact AddMonoidAlgebra.liftNCRingHom f g (fun a p => by
    have hp : g p ∈ Set.center B := (h p.toAdd).toMul.property
    exact Semigroup.mem_center_iff.mp hp (f a))

@[simp] theorem substitute_coefficient {B : Type v} [Ring B] (n : ℕ)
    (f : R →+* B) (values : Fin n → Submonoid.center B) (r : R) :
    substitute n f values (coefficient n r) = f r := by
  simp [substitute, coefficient, AddMonoidAlgebra.singleZeroRingHom_apply,
    AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.singleAddHom_apply]

@[simp] theorem substitute_generator {B : Type v} [Ring B] (n : ℕ)
    (f : R →+* B) (values : Fin n → Submonoid.center B) (j : Fin n) :
    substitute n f values (generator n j) = values j := by
  simp [substitute, generator, AddMonoidAlgebra.liftNCRingHom_single,
    multiplesHom_apply]

/-- Two maps out of a central polynomial ring agree if they agree on the
coefficient ring and on each free coordinate. -/
theorem hom_ext {B : Type v} [Ring B] {n : ℕ} {f g : PolyRing R n →+* B}
    (hcoeff : ∀ r, f (coefficient n r) = g (coefficient n r))
    (hgen : ∀ j, f (generator n j) = g (generator n j)) : f = g := by
  apply AddMonoidAlgebra.ringHom_ext' (by ext r; exact hcoeff r)
  apply Finsupp.mulHom_ext
  intro j a
  induction a with
  | zero => simpa [coefficient] using hcoeff (1 : R)
  | succ a ih =>
    have hs : (Multiplicative.ofAdd (Finsupp.single j (a + 1)) :
        Multiplicative (Fin n →₀ ℕ)) =
        Multiplicative.ofAdd (Finsupp.single j a) *
          Multiplicative.ofAdd (Finsupp.single j 1) := by
      congr 1
      simp [Finsupp.single_add]
    simp only [MonoidHom.comp_apply, hs, map_mul] at ih ⊢
    exact congrArg₂ (· * ·) ih (hgen j)

theorem coordinate_sum (n : ℕ) :
    ∑ j : Fin (n + 1), coordinate (R := R) n j = 1 := by
  simp [Fin.sum_univ_succ, coordinate_zero, coordinate_succ]

/-- The whole fibre sum for an arbitrary ordinal map, including empty fibres. -/
def fiberValue {m n : ℕ} (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (j : Fin (n + 1)) : PolyRing R m :=
  ∑ k : Fin (m + 1), if alpha.toOrderHom k = j then coordinate m k else 0

theorem fiber_mem_center {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (j : Fin (n + 1)) :
    fiberValue (R := R) alpha j ∈ Set.center (PolyRing R m) := by
  unfold fiberValue
  exact Finset.sum_induction _ _ (fun _ _ => Set.add_mem_center)
    (Semigroup.mem_center_iff.mpr (by intro; simp)) (fun k _ => by
      split_ifs <;> [exact coordinate_mem_center m k; exact
        Semigroup.mem_center_iff.mpr (by intro; simp)])

theorem fiber_sum {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ∑ j : Fin (n + 1), fiberValue (R := R) alpha j = 1 := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ) (g := fun k : Fin (m + 1) => alpha.toOrderHom k)
    (f := coordinate (R := R) m) (by simp)
  simp only [Finset.sum_filter] at h
  simpa only [fiberValue, coordinate_sum] using h

/-- The ring homomorphism induced by an ordinal map `alpha : [m] → [n]`.
It points from degree `n` to degree `m`. -/
def ordinalMap {m n : ℕ} (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    PolyRing R n →+* PolyRing R m :=
  substitute n (coefficient m) (fun j =>
    ⟨fiberValue alpha j.succ, fiber_mem_center alpha j.succ⟩)

@[simp] theorem ordinalMap_coefficient {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (r : R) :
    ordinalMap (R := R) alpha (coefficient n r) = coefficient m r :=
  substitute_coefficient ..

@[simp] theorem ordinalMap_generator {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (j : Fin n) :
    ordinalMap (R := R) alpha (generator n j) = fiberValue alpha j.succ :=
  substitute_generator ..

@[simp] theorem ordinalMap_coordinate {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (j : Fin (n + 1)) :
    ordinalMap (R := R) alpha (coordinate n j) = fiberValue alpha j := by
  refine Fin.cases ?_ (fun j => ordinalMap_generator alpha j) j
  have h := fiber_sum (R := R) alpha
  rw [Fin.sum_univ_succ] at h
  have hzero : 1 - ∑ j : Fin n, fiberValue (R := R) alpha j.succ =
      fiberValue alpha 0 := by
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  simpa [coordinate_zero, map_sub, map_one, map_sum, ordinalMap_generator] using hzero

theorem ordinalMap_fiberValue {l m n : ℕ}
    (beta : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (j : Fin (n + 1)) :
    ordinalMap (R := R) beta (fiberValue alpha j) = fiberValue (beta ≫ alpha) j := by
  classical
  simp only [fiberValue, map_sum, apply_ite, map_zero, ordinalMap_coordinate]
  calc
    _ = ∑ k : Fin (m + 1), ∑ a : Fin (l + 1),
          if alpha.toOrderHom k = j ∧ beta.toOrderHom a = k then coordinate l a else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : alpha.toOrderHom k = j <;> simp [hk]
    _ = ∑ a : Fin (l + 1), ∑ k : Fin (m + 1),
          if alpha.toOrderHom k = j ∧ beta.toOrderHom a = k then coordinate l a else 0 :=
      Finset.sum_comm
    _ = ∑ a : Fin (l + 1),
          if alpha.toOrderHom (beta.toOrderHom a) = j then coordinate l a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            simp only [and_comm, ite_and, Finset.sum_ite_eq,
              Finset.mem_univ, ite_true]
    _ = _ := rfl

@[simp] theorem ordinalMap_id (n : ℕ) :
    ordinalMap (R := R) (𝟙 (SimplexCategory.mk n)) = RingHom.id (PolyRing R n) := by
  apply hom_ext
  · intro r; simp
  · intro j
    rw [ordinalMap_generator]
    simp [fiberValue, generator]

@[simp] theorem ordinalMap_comp {l m n : ℕ}
    (beta : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (ordinalMap (R := R) beta).comp (ordinalMap alpha) = ordinalMap (beta ≫ alpha) := by
  apply hom_ext
  · intro r; simp
  · intro j
    simpa only [RingHom.comp_apply, ordinalMap_generator] using
      ordinalMap_fiberValue (R := R) beta alpha j.succ

/-- Coefficient maps leave all central indeterminates fixed. -/
def coefficientMap {S : Type v} [Ring S] (phi : R →+* S) (n : ℕ) :
    PolyRing R n →+* PolyRing S n :=
  AddMonoidAlgebra.mapRingHom (Fin n →₀ ℕ) phi

@[simp] theorem coefficientMap_coefficient {S : Type v} [Ring S]
    (phi : R →+* S) (n : ℕ) (r : R) :
    coefficientMap phi n (coefficient n r) = coefficient n (phi r) := by
  simp [coefficientMap, coefficient, AddMonoidAlgebra.mapRingHom_single]

@[simp] theorem coefficientMap_generator {S : Type v} [Ring S]
    (phi : R →+* S) (n : ℕ) (j : Fin n) :
    coefficientMap phi n (generator n j) = generator n j := by
  simp [coefficientMap, generator, AddMonoidAlgebra.mapRingHom_single]

@[simp] theorem coefficientMap_coordinate {S : Type v} [Ring S]
    (phi : R →+* S) (n : ℕ) (j : Fin (n + 1)) :
    coefficientMap phi n (coordinate n j) = coordinate n j := by
  refine Fin.cases ?_ (fun j => coefficientMap_generator phi n j) j
  simp [coordinate_zero, map_sub, map_sum, coefficientMap_generator]

@[simp] theorem coefficientMap_id (n : ℕ) :
    coefficientMap (R := R) (RingHom.id R) n = RingHom.id (PolyRing R n) :=
  AddMonoidAlgebra.mapRingHom_id

@[simp] theorem coefficientMap_comp {S : Type v} {T : Type*}
    [Ring S] [Ring T] (phi : R →+* S) (psi : S →+* T) (n : ℕ) :
    (coefficientMap psi n).comp (coefficientMap phi n) =
      coefficientMap (psi.comp phi) n := by
  exact (AddMonoidAlgebra.mapRingHom_comp psi phi).symm

/-- Coefficient homomorphisms commute with *every* ordinal substitution. -/
theorem coefficientMap_ordinalMap {S : Type v} [Ring S] (phi : R →+* S)
    {m n : ℕ} (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (coefficientMap phi m).comp (ordinalMap (R := R) alpha) =
      (ordinalMap (R := S) alpha).comp (coefficientMap phi n) := by
  apply hom_ext
  · intro r; simp
  · intro j
    simp only [RingHom.comp_apply, ordinalMap_generator, coefficientMap_generator]
    unfold fiberValue
    simp only [map_sum, apply_ite, map_zero, coefficientMap_coordinate]

/-- The simplicial central-polynomial ring of an arbitrary unital ring. -/
def simplex (A : RingCat.{u}) : SimplicialObject RingCat.{u} where
  obj x := RingCat.of (PolyRing A x.unop.len)
  map f := RingCat.ofHom (ordinalMap (R := A) f.unop)
  map_id x := by
    apply RingCat.hom_ext
    exact ordinalMap_id (R := A) x.unop.len
  map_comp f g := by
    apply RingCat.hom_ext
    exact (ordinalMap_comp (R := A) g.unop f.unop).symm

/-- Functoriality of central-polynomial simplices in the coefficient ring. -/
def coefficientNatural {A B : RingCat.{u}} (phi : A ⟶ B) :
    simplex A ⟶ simplex B where
  app x := RingCat.ofHom (coefficientMap phi.hom x.unop.len)
  naturality := by
    intro x y f
    apply RingCat.hom_ext
    exact coefficientMap_ordinalMap phi.hom f.unop

/-- The actual functor from rings to simplicial rings, not merely degreewise maps. -/
def simplexFunctor : RingCat.{u} ⥤ SimplicialObject RingCat.{u} where
  obj := simplex
  map := coefficientNatural
  map_id A := by
    apply NatTrans.ext
    funext x
    apply RingCat.hom_ext
    exact coefficientMap_id (R := A) x.unop.len
  map_comp phi psi := by
    apply NatTrans.ext
    funext x
    apply RingCat.hom_ext
    exact (coefficientMap_comp phi.hom psi.hom x.unop.len).symm

/-- Polynomial extension by one further central variable as a functor on rings. -/
def polynomialFunctor : RingCat.{u} ⥤ RingCat.{u} where
  obj A := RingCat.of (Polynomial A)
  map phi := RingCat.ofHom (Polynomial.mapRingHom phi.hom)
  map_id A := by
    apply RingCat.hom_ext
    exact Polynomial.mapRingHom_id
  map_comp phi psi := by
    apply RingCat.hom_ext
    exact (Polynomial.mapRingHom_comp psi.hom phi.hom).symm

/-- Degreewise coefficient inclusion, bundled as a map of simplicial rings. -/
def constantInclusion (A : RingCat.{u}) :
    simplex A ⟶ simplex (polynomialFunctor.obj A) :=
  coefficientNatural (RingCat.ofHom (Polynomial.C (R := A)))

/-- Degreewise constant-term evaluation, bundled as a map of simplicial rings. -/
def evalAtZero (A : RingCat.{u}) :
    simplex (polynomialFunctor.obj A) ⟶ simplex A :=
  coefficientNatural (RingCat.ofHom (Polynomial.constantCoeff (R := A)))

/-- Evaluation at zero retracts the inclusion, as an identity of actual
simplicial-ring morphisms. This is not a homotopy equivalence claim. -/
theorem constantInclusion_evalAtZero (A : RingCat.{u}) :
    constantInclusion A ≫ evalAtZero A = 𝟙 (simplex A) := by
  apply NatTrans.ext
  funext x
  apply RingCat.hom_ext
  change (coefficientMap (Polynomial.constantCoeff (R := A)) x.unop.len).comp
    (coefficientMap (Polynomial.C (R := A)) x.unop.len) =
      RingHom.id (PolyRing A x.unop.len)
  rw [coefficientMap_comp]
  have h : (Polynomial.constantCoeff (R := A)).comp Polynomial.C = RingHom.id A := by
    ext r
    simp [Polynomial.constantCoeff]
  rw [h, coefficientMap_id]

/-- Coefficient inclusion is natural in the coefficient ring. -/
def constantTransformation : simplexFunctor ⟶ polynomialFunctor ⋙ simplexFunctor where
  app A := constantInclusion A
  naturality := by
    intro A B phi
    apply NatTrans.ext
    funext x
    apply RingCat.hom_ext
    change (coefficientMap (Polynomial.C (R := _)) x.unop.len).comp
      (coefficientMap phi.hom x.unop.len) =
        (coefficientMap (Polynomial.mapRingHom phi.hom) x.unop.len).comp
          (coefficientMap (Polynomial.C (R := _)) x.unop.len)
    rw [coefficientMap_comp, coefficientMap_comp]
    exact congrArg (fun hom => coefficientMap hom x.unop.len)
      (Polynomial.mapRingHom_comp_C phi.hom).symm

/-- Constant-term evaluation is natural in the coefficient ring. -/
def evaluationTransformation : polynomialFunctor ⋙ simplexFunctor ⟶ simplexFunctor where
  app A := evalAtZero A
  naturality := by
    intro A B phi
    apply NatTrans.ext
    funext x
    apply RingCat.hom_ext
    change (coefficientMap (Polynomial.constantCoeff (R := _)) x.unop.len).comp
      (coefficientMap (Polynomial.mapRingHom phi.hom) x.unop.len) =
        (coefficientMap phi.hom x.unop.len).comp
          (coefficientMap (Polynomial.constantCoeff (R := _)) x.unop.len)
    rw [coefficientMap_comp, coefficientMap_comp]
    have h : (Polynomial.constantCoeff (R := _)).comp
        (Polynomial.mapRingHom phi.hom) =
        phi.hom.comp (Polynomial.constantCoeff (R := _)) := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [Polynomial.constantCoeff]
      · simp [Polynomial.constantCoeff]
    exact congrArg (fun hom => coefficientMap hom x.unop.len) h

/-- The splitting also holds as an equality of coefficient-natural transformations. -/
theorem constantTransformation_evaluationTransformation :
    constantTransformation ≫ evaluationTransformation = 𝟙 simplexFunctor := by
  apply NatTrans.ext
  funext A
  change constantInclusion A ≫ evalAtZero A = 𝟙 (simplex A)
  exact constantInclusion_evalAtZero A

/-- Computing the value of the simplicial functor in degree `n`. -/
theorem simplexFunctor_degree (A : RingCat.{u}) (n : ℕ) :
    (simplexFunctor.obj A).obj (Opposite.op (SimplexCategory.mk n)) =
      RingCat.of (PolyRing A n) := rfl

theorem simplexFunctor_ordinal (A : RingCat.{u}) {m n : ℕ}
    (alpha : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    ((simplexFunctor.obj A).map alpha.op).hom = ordinalMap (R := A) alpha := rfl

@[simp] theorem constantInclusion_coefficient (A : RingCat.{u}) (n : ℕ) (r : A) :
    (constantInclusion A).app (Opposite.op (SimplexCategory.mk n))
      (coefficient n r) = coefficient n (Polynomial.C r) :=
  coefficientMap_coefficient ..

@[simp] theorem constantInclusion_generator (A : RingCat.{u}) (n : ℕ) (j : Fin n) :
    (constantInclusion A).app (Opposite.op (SimplexCategory.mk n))
      (generator n j) = generator n j := coefficientMap_generator ..

@[simp] theorem evalAtZero_coefficient (A : RingCat.{u}) (n : ℕ) (p : Polynomial A) :
    (evalAtZero A).app (Opposite.op (SimplexCategory.mk n))
      (coefficient n p) = coefficient n (Polynomial.constantCoeff p) :=
  coefficientMap_coefficient ..

@[simp] theorem evalAtZero_generator (A : RingCat.{u}) (n : ℕ) (j : Fin n) :
    (evalAtZero A).app (Opposite.op (SimplexCategory.mk n))
      (generator n j) = generator n j := coefficientMap_generator ..

end
end CentralPolynomialSimplex
