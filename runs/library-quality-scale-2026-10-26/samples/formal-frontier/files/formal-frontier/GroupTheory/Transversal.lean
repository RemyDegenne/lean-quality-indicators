/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Complement

/-!
# Right-transversal calculations and subgroup towers

For a right transversal `T` of `H`, `factor` and `next` describe the unique
factorization of `t * g` into an element of `H` followed by a representative in
`T`. They give permutations of representatives and changes of transversal.

For `K ≤ G` and `J ≤ K`, products of an inner and an outer representative,
in that order, form a right transversal of `J.map K.subtype` in `G`. For a
presentation `H ≤ K` by ambient subgroups, the inner subgroup is
`H.comap K.subtype`. No finiteness or normality hypothesis is needed.

These constructions generalize the pure representative calculations in the
Continuous Group Cohomology formalization
from `Corestriction` and `Composition`. They reuse Mathlib's complement
and injective subgroup-image equivalences.
-/

@[expose] public section

noncomputable section

universe u

namespace Subgroup.RightTransversal

variable {G : Type u} [Group G]

section Representatives

variable {H : Subgroup G} (T : H.RightTransversal)

/-- The subgroup factor in the decomposition of `t * g`. -/
def factor (t : ↥(T : Set G)) (g : G) : H := (T.2.equiv ((t : G) * g)).1

/-- The chosen representative in the decomposition of `t * g`. -/
def next (t : ↥(T : Set G)) (g : G) : ↥(T : Set G) :=
  (T.2.equiv ((t : G) * g)).2

/-- Multiplying the two coordinates recovers `t * g`. -/
lemma factor_mul_next (t : ↥(T : Set G)) (g : G) :
    (factor T t g : G) * (next T t g : G) = (t : G) * g :=
  T.2.equiv_fst_mul_equiv_snd _

lemma next_one (t : ↥(T : Set G)) : next T t 1 = t := by
  apply Subtype.ext
  simpa [next] using congrArg Subtype.val
    (T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.2)

lemma factor_one (t : ↥(T : Set G)) : factor T t 1 = 1 := by
  apply Subtype.ext
  simpa [factor] using T.2.coe_equiv_fst_eq_one_iff_mem H.one_mem |>.2 t.2

/-- Decomposing a product agrees with successive decompositions. -/
lemma equiv_mul (t : ↥(T : Set G)) (g g' : G) :
    T.2.equiv ((t : G) * (g * g')) =
      (factor T t g * factor T (next T t g) g', next T (next T t g) g') := by
  rw [← mul_assoc, ← factor_mul_next T t g, mul_assoc, T.2.equiv_mul_left]
  rfl

lemma factor_mul (t : ↥(T : Set G)) (g g' : G) :
    factor T t (g * g') = factor T t g * factor T (next T t g) g' :=
  congrArg Prod.fst (equiv_mul T t g g')

lemma next_mul (t : ↥(T : Set G)) (g g' : G) :
    next T t (g * g') = next T (next T t g) g' := by
  simpa only [next] using congrArg Prod.snd (equiv_mul T t g g')

/-- An inverse form of the representative decomposition. -/
lemma inv_mul_factor (t : ↥(T : Set G)) (g : G) :
    (t : G)⁻¹ * (factor T t g : G) = g * (next T t g : G)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).2
  calc
    ((t : G)⁻¹ * (factor T t g : G)) * (next T t g : G) =
        (t : G)⁻¹ * ((factor T t g : G) * (next T t g : G)) := by
          rw [mul_assoc]
    _ = (t : G)⁻¹ * ((t : G) * g) := by rw [factor_mul_next]
    _ = g := by simp

/-- Right multiplication permutes the chosen right-transversal representatives. -/
def nextEquiv (g : G) : ↥(T : Set G) ≃ ↥(T : Set G) where
  toFun t := next T t g
  invFun t := next T t g⁻¹
  left_inv t := by
    change next T (next T t g) g⁻¹ = t
    rw [← next_mul, mul_inv_cancel, next_one]
  right_inv t := by
    change next T (next T t g⁻¹) g = t
    rw [← next_mul, inv_mul_cancel, next_one]

@[simp]
lemma nextEquiv_apply (g : G) (t : ↥(T : Set G)) :
    nextEquiv T g t = next T t g := rfl

@[simp]
lemma nextEquiv_symm_apply (g : G) (t : ↥(T : Set G)) :
    (nextEquiv T g).symm t = next T t g⁻¹ := rfl

/-- The subgroup correction matching a representative in `T` with one in `S`. -/
def changeFactor (S : H.RightTransversal) (t : ↥(T : Set G)) : H :=
  (S.2.equiv (t : G)).1

/-- The representative in `S` of the same right coset as a representative in `T`. -/
def changeRep (S : H.RightTransversal) (t : ↥(T : Set G)) : ↥(S : Set G) :=
  (S.2.equiv (t : G)).2

lemma changeFactor_mul_changeRep (S : H.RightTransversal) (t : ↥(T : Set G)) :
    (changeFactor T S t : G) * (changeRep T S t : G) = (t : G) :=
  S.2.equiv_fst_mul_equiv_snd _

lemma changeRep_rightCoset (S : H.RightTransversal) (t : ↥(T : Set G)) :
    RightCosetEquivalence (H : Set G) (changeRep T S t : G) (t : G) := by
  rw [RightCosetEquivalence, rightCoset_eq_iff H]
  rw [← changeFactor_mul_changeRep T S t]
  simp only [mul_inv_cancel_right]
  exact (changeFactor T S t).2

/-- Matching representatives of two right transversals gives an equivalence. -/
def changeRepEquiv (S : H.RightTransversal) :
    ↥(T : Set G) ≃ ↥(S : Set G) where
  toFun := changeRep T S
  invFun := changeRep S T
  left_inv t := by
    change (T.2.equiv (changeRep T S t : G)).2 = t
    calc
      _ = (T.2.equiv (t : G)).2 :=
        T.2.equiv_snd_eq_iff_rightCosetEquivalence.2 (changeRep_rightCoset T S t)
      _ = t := T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.2
  right_inv s := by
    change (S.2.equiv (changeRep S T s : G)).2 = s
    calc
      _ = (S.2.equiv (s : G)).2 :=
        S.2.equiv_snd_eq_iff_rightCosetEquivalence.2 (changeRep_rightCoset S T s)
      _ = s := S.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem s.2

@[simp]
lemma changeRepEquiv_apply (S : H.RightTransversal) (t : ↥(T : Set G)) :
    changeRepEquiv T S t = changeRep T S t := rfl

@[simp]
lemma changeRepEquiv_symm_apply (S : H.RightTransversal) (s : ↥(S : Set G)) :
    (changeRepEquiv T S).symm s = changeRep S T s := rfl

end Representatives

/-- The product of an inner and an outer right-transversal representative. -/
def towerRep (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal)
    (p : ↥(U : Set K) × ↥(T : Set G)) : G :=
  (p.1 : K) * (p.2 : G)

@[simp]
lemma towerRep_apply (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal)
    (p : ↥(U : Set K) × ↥(T : Set G)) :
    towerRep K J U T p = ((p.1 : K) : G) * (p.2 : G) := rfl

lemma towerRep_injective (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    Function.Injective (towerRep K J U T) := by
  intro a b hab
  have hpair : ((a.1 : K), a.2) = ((b.1 : K), b.2) := T.2.1 hab
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun p => (p.1 : K)) hpair)
  · exact congrArg (fun p : K × ↥(T : Set G) => p.2) hpair

/-- The canonical indexing equivalence for the range of representative products. -/
def towerRepEquiv (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    (↥(U : Set K) × ↥(T : Set G)) ≃ Set.range (towerRep K J U T) :=
  Equiv.ofInjective (towerRep K J U T) (towerRep_injective K J U T)

@[simp]
lemma towerRepEquiv_apply_coe (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal)
    (p : ↥(U : Set K) × ↥(T : Set G)) :
    (towerRepEquiv K J U T p : G) = towerRep K J U T p := rfl

/-- Decompose an ambient group element successively along a subgroup tower. -/
def towerDecompositionEquiv (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    G ≃ J × (↥(U : Set K) × ↥(T : Set G)) :=
  T.2.equiv |>.trans <|
    (Equiv.prodCongr U.2.equiv (Equiv.refl _)).trans
      (Equiv.prodAssoc J ↥(U : Set K) ↥(T : Set G))

@[simp]
lemma towerDecompositionEquiv_symm_apply (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal)
    (j : J) (p : ↥(U : Set K) × ↥(T : Set G)) :
    (towerDecompositionEquiv K J U T).symm (j, p) =
      ((((j : K) : G) * ((p.1 : K) : G)) * (p.2 : G)) := by
  change T.2.equiv.symm (U.2.equiv.symm (j, p.1), p.2) = _
  rw [T.2.equiv_symm_apply, U.2.equiv_symm_apply]
  rfl

/-- Products of inner and outer representatives form a right transversal of the
flattened subgroup. The carrier is the range of `towerRep`. -/
def transRightTransversal (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    (J.map K.subtype).RightTransversal := by
  let P : Set G := Set.range (towerRep K J U T)
  let eP : (↥(U : Set K) × ↥(T : Set G)) ≃ P := towerRepEquiv K J U T
  let eJ : J ≃* J.map K.subtype :=
    J.equivMapOfInjective K.subtype K.subtype_injective
  let eD : J × (↥(U : Set K) × ↥(T : Set G)) ≃ (J.map K.subtype) × P :=
    Equiv.prodCongr eJ.toEquiv eP
  refine ⟨P, ?_⟩
  change Function.Bijective (fun p : (J.map K.subtype) × P =>
    (p.1 : G) * (p.2 : G))
  have hb := (eD.symm.trans (towerDecompositionEquiv K J U T).symm).bijective
  convert hb using 1
  funext p
  rcases p with ⟨j, p⟩
  rcases p.2 with ⟨ut, hut⟩
  have hp : eP ut = p := Subtype.ext hut
  subst p
  change (j : G) * (towerRepEquiv K J U T ut : G) =
    (towerDecompositionEquiv K J U T).symm (eJ.symm j, eP.symm (eP ut))
  rw [Equiv.symm_apply_apply, towerDecompositionEquiv_symm_apply,
    towerRepEquiv_apply_coe, towerRep_apply]
  have hj : (((eJ.symm j : J) : K) : G) = (j : G) :=
    congrArg (fun x : J.map K.subtype => (x : G)) (eJ.apply_symm_apply j)
  rw [hj, mul_assoc]

@[simp]
lemma coe_transRightTransversal (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    (transRightTransversal K J U T : Set G) =
      Set.range (towerRep K J U T) := rfl

/-- Product indexing with the actual composite transversal as codomain. -/
def transRightRepEquiv (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal) :
    (↥(U : Set K) × ↥(T : Set G)) ≃
      ↥(transRightTransversal K J U T : Set G) :=
  Equiv.ofBijective
    (fun p => ⟨towerRep K J U T p, by
      rw [coe_transRightTransversal]
      exact ⟨p, rfl⟩⟩)
    ⟨fun _ _ h => towerRep_injective K J U T (Subtype.ext_iff.mp h),
      fun q => by
        have hq : (q : G) ∈ Set.range (towerRep K J U T) := by
          rw [← coe_transRightTransversal]
          exact q.2
        rcases hq with ⟨p, hp⟩
        refine ⟨p, ?_⟩
        apply Subtype.ext
        exact hp⟩

@[simp]
lemma transRightRepEquiv_apply_coe (K : Subgroup G) (J : Subgroup K)
    (U : J.RightTransversal) (T : K.RightTransversal)
    (p : ↥(U : Set K) × ↥(T : Set G)) :
    (transRightRepEquiv K J U T p : G) = towerRep K J U T p := rfl

end Subgroup.RightTransversal
