/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Pi
public import StableRange.RepeatedBlock

/-!
# Row rank over division rings

This file defines the row rank of a matrix over a possibly noncommutative
division ring as the dimension of the range of its left-linear row-vector map
for right matrix multiplication. It proves the usual zero, identity,
multiplication, orthogonal-idempotent, and repeated-diagonal-block properties
and realizes every possible finite square-matrix row rank. It also packages
the normalized real-valued row rank for nonempty finite square matrices.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  the rank-function paragraph and Exercise I.1.13(d) (finite matrix ranks).
* Mathlib, `LinearAlgebra.FiniteDimensional.Lemmas`, `Dimension.Constructions`
  and `Matrix.ToLin` (finrank and the row-vector linear map).
-/

set_option warningAsError true

@[expose] public section

open Function
open scoped Kronecker

universe u v w x y

namespace Matrix

variable {K : Type u} [DivisionRing K]
variable {m : Type v} {n : Type w} {p : Type x}
variable [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- The row rank of a matrix over a possibly noncommutative division ring. -/
noncomputable def rowRank (A : Matrix m n K) : ℕ :=
  Module.finrank K (LinearMap.range A.toLinearMapRight')

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem rowRank_zero : rowRank (0 : Matrix m n K) = 0 := by
  simp [rowRank]

@[simp]
theorem rowRank_one : rowRank (1 : Matrix n n K) = Fintype.card n := by
  rw [rowRank, toLinearMapRight'_one, LinearMap.range_id, finrank_top,
    Module.finrank_eq_card_basis (Pi.basisFun K n)]

omit [DecidableEq n] in
theorem rowRank_le_card (A : Matrix m n K) :
    rowRank A ≤ Fintype.card n := by
  exact (Submodule.finrank_le (LinearMap.range A.toLinearMapRight')).trans_eq
    (Module.finrank_eq_card_basis (Pi.basisFun K n))

omit [Fintype n] [DecidableEq n] in
theorem rowRank_eq_zero_iff (A : Matrix m n K) : rowRank A = 0 ↔ A = 0 := by
  rw [rowRank, Submodule.finrank_eq_zero]
  constructor
  · intro h
    apply toLinearMapRight'.injective
    calc
      toLinearMapRight' A = 0 := LinearMap.range_eq_bot.mp h
      _ = toLinearMapRight' 0 := (toLinearMapRight'.map_zero).symm
  · intro h
    rw [h]
    simp

omit [Fintype n] [DecidableEq n] in
theorem rowRank_pos_iff (A : Matrix m n K) : 0 < rowRank A ↔ A ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, rowRank_eq_zero_iff]

section Reindex

variable {m' : Type x} {n' : Type y} [Fintype m'] [DecidableEq m']

/-- Reindex coordinate functions along an equivalence. -/
private def reindexCoordinates {a : Type v} {a' : Type w}
    (e : a ≃ a') : (a → K) ≃ₗ[K] (a' → K) where
  toFun v i := v (e.symm i)
  invFun v i := v (e i)
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
/-- Reindexing a matrix conjugates its row-vector right-multiplication map by
the corresponding coordinate equivalences. -/
private theorem toLinearMapRight'_reindex (er : m ≃ m') (ec : n ≃ n')
    (A : Matrix m n K) :
    (reindex er ec A).toLinearMapRight' =
      (reindexCoordinates ec).toLinearMap.comp
        (A.toLinearMapRight'.comp
          (reindexCoordinates er).symm.toLinearMap) := by
  apply LinearMap.ext
  intro v
  funext j
  change vecMul v (A.submatrix er.symm ec.symm) j =
    vecMul (v ∘ er) A (ec.symm j)
  exact congrFun (submatrix_vecMul_equiv A v er.symm ec.symm) j

omit [Fintype n] [DecidableEq n] in
/-- Independently reindexing the rows and columns of a rectangular matrix does
not change its row rank. -/
theorem rowRank_reindex (er : m ≃ m') (ec : n ≃ n') (A : Matrix m n K) :
    rowRank (reindex er ec A) = rowRank A := by
  rw [rowRank, rowRank, toLinearMapRight'_reindex]
  rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq]

end Reindex

private def rankProjection (k l : ℕ) :
    Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K :=
  Matrix.fromBlocks 1 0 0 0

private noncomputable def rankProjectionRangeEquiv (k l : ℕ) :
    LinearMap.range (rankProjection (K := K) k l).toLinearMapRight' ≃ₗ[K]
      (Fin k → K) where
  toFun z i := z.1 (Sum.inl i)
  invFun x := ⟨Sum.elim x 0, by
    refine ⟨Sum.elim x 0, ?_⟩
    change (Sum.elim x 0) ᵥ* rankProjection (K := K) k l = Sum.elim x 0
    funext i
    cases i <;> simp [rankProjection, Matrix.vecMul_fromBlocks]⟩
  left_inv z := by
    obtain ⟨z, v, rfl⟩ := z
    apply Subtype.ext
    funext i
    cases i <;> simp [rankProjection, Matrix.vecMul_fromBlocks]
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem rowRank_rankProjection (k l : ℕ) :
    rowRank (rankProjection (K := K) k l) = k := by
  rw [rowRank]
  rw [LinearEquiv.finrank_eq (rankProjectionRangeEquiv (K := K) k l)]
  simp [Module.finrank_eq_card_basis (Pi.basisFun K (Fin k))]

/-- Every natural number bounded by the size of a finite square matrix occurs
as the row rank of such a matrix over a division ring. -/
theorem exists_rowRank_eq (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∃ A : Matrix n n K, rowRank A = k := by
  let e : Fin k ⊕ Fin (Fintype.card n - k) ≃ n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hk)) |>.trans
      (Fintype.equivFin n).symm
  refine ⟨(rankProjection (K := K) k (Fintype.card n - k)).reindex e e, ?_⟩
  rw [rowRank_reindex, rowRank_rankProjection]

omit [Fintype p] [DecidableEq p] [DecidableEq n] in
theorem rowRank_mul_le_left (A : Matrix m n K) (B : Matrix n p K) :
    rowRank (A * B) ≤ rowRank A := by
  classical
  rw [rowRank, rowRank, toLinearMapRight'_mul, LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

omit [Fintype p] [DecidableEq p] in
theorem rowRank_mul_le_right (A : Matrix m n K) (B : Matrix n p K) :
    rowRank (A * B) ≤ rowRank B := by
  rw [rowRank, rowRank, toLinearMapRight'_mul]
  exact Submodule.finrank_mono
    (LinearMap.range_comp_le_range A.toLinearMapRight' B.toLinearMapRight')

theorem rowRank_add_of_orthogonal_idempotents
    (E G : Matrix n n K)
    (hEE : E * E = E) (hGG : G * G = G)
    (hEG : E * G = 0) (hGE : G * E = 0) :
    rowRank (E + G) = rowRank E + rowRank G := by
  let e : Module.End K (n → K) := E.toLinearMapRight'
  let g : Module.End K (n → K) := G.toLinearMapRight'
  have hee : e.comp e = e := by
    simpa only [e, toLinearMapRight'_mul] using
      congrArg toLinearMapRight' hEE
  have hgg : g.comp g = g := by
    simpa only [g, toLinearMapRight'_mul] using
      congrArg toLinearMapRight' hGG
  have hge : g.comp e = 0 := by
    simpa only [e, g, toLinearMapRight'_mul, LinearEquiv.map_zero] using
      congrArg toLinearMapRight' hEG
  have heg : e.comp g = 0 := by
    simpa only [e, g, toLinearMapRight'_mul, LinearEquiv.map_zero] using
      congrArg toLinearMapRight' hGE
  have hee_apply (a) : e (e a) = e a := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hee a
  have hgg_apply (a) : g (g a) = g a := by
    simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hgg a
  have hge_apply (a) : g (e a) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun hge a
  have heg_apply (a) : e (g a) = 0 := by
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun heg a
  have hdisjoint : Disjoint (LinearMap.range e) (LinearMap.range g) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    rintro a ⟨haE, haG⟩
    obtain ⟨b, rfl⟩ := haE
    obtain ⟨c, hc⟩ := haG
    have heb : e (e b) = e b := hee_apply b
    have heb0 : e (e b) = 0 := by
      rw [← hc]
      exact heg_apply c
    simpa only [Submodule.mem_bot] using heb.symm.trans heb0
  have hrange : LinearMap.range (e + g) =
      LinearMap.range e ⊔ LinearMap.range g := by
    apply le_antisymm (LinearMap.range_add_le e g)
    rw [sup_le_iff]
    constructor
    · rintro a ⟨b, rfl⟩
      refine ⟨e b, ?_⟩
      simp only [LinearMap.add_apply]
      rw [hee_apply b, hge_apply b, add_zero]
    · rintro a ⟨b, rfl⟩
      refine ⟨g b, ?_⟩
      simp only [LinearMap.add_apply]
      rw [heg_apply b, hgg_apply b, zero_add]
  rw [rowRank, rowRank, rowRank, LinearEquiv.map_add]
  change Module.finrank K (LinearMap.range (e + g)) =
    Module.finrank K (LinearMap.range e) + Module.finrank K (LinearMap.range g)
  rw [hrange, ← Submodule.finrank_sup_add_finrank_inf_eq,
    hdisjoint.eq_bot, finrank_bot, add_zero]

section RepeatedBlocks

variable {o : Type y} [Fintype o] [DecidableEq o]

/-- Swap product coordinates so repeated-block multiplication becomes a
pointwise family of copies of the original row-vector map. -/
private def repeatBlockCoordinates (a : Type v) :
    ((a × o) → K) ≃ₗ[K] (o → a → K) where
  toFun v k i := v (i, k)
  invFun v ik := v ik.2 ik.1
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
private theorem repeatBlockCoordinates_apply (A : Matrix m n K)
    (v : (m × o) → K) :
    repeatBlockCoordinates (o := o) n
        ((repeatBlock (o := o) A).toLinearMapRight' v) =
      (A.toLinearMapRight'.compLeft o)
        (repeatBlockCoordinates (o := o) m v) := by
  ext k j
  change (∑ x : m × o, v x * blockDiagonal (fun _ : o => A) x (j, k)) =
    ∑ i : m, v (i, k) * A i j
  rw [Fintype.sum_prod_type]
  simp only [blockDiagonal_apply]
  simp

/-- Coordinate swapping restricted to the range of a repeated-block matrix. -/
private noncomputable def repeatBlockRangeMap (A : Matrix m n K) :
    LinearMap.range (repeatBlock (o := o) A).toLinearMapRight' →ₗ[K]
      (o → LinearMap.range A.toLinearMapRight') where
  toFun z k := ⟨repeatBlockCoordinates (o := o) n z.1 k, by
    rcases z.2 with ⟨v, hv⟩
    refine ⟨repeatBlockCoordinates (o := o) m v k, ?_⟩
    calc
      A.toLinearMapRight' (repeatBlockCoordinates (o := o) m v k) =
          repeatBlockCoordinates (o := o) n
            ((repeatBlock (o := o) A).toLinearMapRight' v) k :=
        (congrFun (repeatBlockCoordinates_apply (o := o) A v) k).symm
      _ = repeatBlockCoordinates (o := o) n z.1 k := congrArg
        (fun q => repeatBlockCoordinates (o := o) n q k) hv⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype n] [DecidableEq n] in
private theorem repeatBlockRangeMap_injective (A : Matrix m n K) :
    Function.Injective (repeatBlockRangeMap (o := o) A) := by
  intro z z' h
  apply Subtype.ext
  apply (repeatBlockCoordinates (o := o) n).injective
  funext k
  exact congrArg Subtype.val (congrFun h k)

omit [Fintype n] [DecidableEq n] in
private theorem repeatBlockRangeMap_surjective (A : Matrix m n K) :
    Function.Surjective (repeatBlockRangeMap (o := o) A) := by
  intro z
  choose v hv using fun k => (z k).2
  let w : (m × o) → K :=
    (repeatBlockCoordinates (o := o) m).symm (fun k => v k)
  let x : (n × o) → K :=
    (repeatBlockCoordinates (o := o) n).symm (fun k => (z k).1)
  have hx : x ∈ LinearMap.range
      (repeatBlock (o := o) A).toLinearMapRight' := by
    refine ⟨w, ?_⟩
    apply (repeatBlockCoordinates (o := o) n).injective
    rw [repeatBlockCoordinates_apply]
    ext k i
    simpa [w, x] using congrFun (hv k) i
  refine ⟨⟨x, hx⟩, ?_⟩
  funext k
  apply Subtype.ext
  rfl

/-- The range of a repeated-block matrix is a finite family of copies of the
range of the original matrix. -/
private noncomputable def repeatBlockRangeEquiv (A : Matrix m n K) :
    LinearMap.range (repeatBlock (o := o) A).toLinearMapRight' ≃ₗ[K]
      (o → LinearMap.range A.toLinearMapRight') :=
  LinearEquiv.ofBijective (repeatBlockRangeMap (o := o) A)
    ⟨repeatBlockRangeMap_injective (o := o) A,
      repeatBlockRangeMap_surjective (o := o) A⟩

omit [Fintype n] [DecidableEq n] in
/-- Repeating a matrix on `o` diagonal blocks multiplies its row rank by the
number of blocks. -/
theorem rowRank_repeatBlock (A : Matrix m n K) :
    rowRank (repeatBlock (o := o) A) = Fintype.card o * rowRank A := by
  rw [rowRank, rowRank]
  rw [(repeatBlockRangeEquiv (o := o) A).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp

end RepeatedBlocks

/-- Row rank divided by the size of a finite square matrix, as a real number;
compare Weibel, *The K-book*, Exercise I.1.13(d), for positive matrix size. -/
noncomputable def normalizedRowRank (A : Matrix n n K) : ℝ :=
  (rowRank A : ℝ) / Fintype.card n

/-- Every quotient `k / card n` with `k ≤ card n` occurs as the normalized
row rank of a square matrix over a division ring. -/
theorem exists_normalizedRowRank_eq (k : ℕ) (hk : k ≤ Fintype.card n) :
    ∃ A : Matrix n n K,
      normalizedRowRank A = (k : ℝ) / Fintype.card n := by
  obtain ⟨A, hA⟩ := exists_rowRank_eq (K := K) k hk
  exact ⟨A, by rw [normalizedRowRank, hA]⟩

section Reindex

variable {n' : Type y} [Fintype n'] [DecidableEq n']

/-- Simultaneously reindexing a finite square matrix does not change its
normalized row rank. -/
theorem normalizedRowRank_reindex (e : n ≃ n') (A : Matrix n n K) :
    normalizedRowRank (reindex e e A) = normalizedRowRank A := by
  rw [normalizedRowRank, normalizedRowRank, rowRank_reindex,
    Fintype.card_congr e]

end Reindex

section PositiveSize

variable [Nonempty n]

omit [DecidableEq n] in
private theorem card_cast_pos : (0 : ℝ) < Fintype.card n := by
  exact_mod_cast Fintype.card_pos

theorem normalizedRowRank_mem_Icc (A : Matrix n n K) :
    normalizedRowRank A ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) card_cast_pos.le
  · have hcast : (rowRank A : ℝ) ≤ (Fintype.card n : ℝ) := by
      exact_mod_cast rowRank_le_card A
    calc
      normalizedRowRank A ≤ (Fintype.card n : ℝ) / Fintype.card n :=
        (div_le_div_iff_of_pos_right card_cast_pos).2 hcast
      _ = 1 := div_self card_cast_pos.ne'

omit [Nonempty n] in
@[simp]
theorem normalizedRowRank_zero :
    normalizedRowRank (0 : Matrix n n K) = 0 := by
  simp [normalizedRowRank]

@[simp]
theorem normalizedRowRank_one :
    normalizedRowRank (1 : Matrix n n K) = 1 := by
  simp [normalizedRowRank, card_cast_pos.ne']

theorem normalizedRowRank_pos_iff (A : Matrix n n K) :
    0 < normalizedRowRank A ↔ A ≠ 0 := by
  rw [normalizedRowRank, div_pos_iff_of_pos_right card_cast_pos,
    Nat.cast_pos, rowRank_pos_iff]

theorem normalizedRowRank_mul_le_left (A B : Matrix n n K) :
    normalizedRowRank (A * B) ≤ normalizedRowRank A := by
  exact (div_le_div_iff_of_pos_right card_cast_pos).2
    (by exact_mod_cast rowRank_mul_le_left A B)

theorem normalizedRowRank_mul_le_right (A B : Matrix n n K) :
    normalizedRowRank (A * B) ≤ normalizedRowRank B := by
  exact (div_le_div_iff_of_pos_right card_cast_pos).2
    (by exact_mod_cast rowRank_mul_le_right A B)

omit [Nonempty n] in
theorem normalizedRowRank_add_of_orthogonal_idempotents
    (E G : Matrix n n K)
    (hEE : E * E = E) (hGG : G * G = G)
    (hEG : E * G = 0) (hGE : G * E = 0) :
    normalizedRowRank (E + G) = normalizedRowRank E + normalizedRowRank G := by
  simp only [normalizedRowRank,
    rowRank_add_of_orthogonal_idempotents E G hEE hGG hEG hGE,
    Nat.cast_add, add_div]

variable {o : Type y} [Fintype o] [DecidableEq o] [Nonempty o]

/-- Repeating a nonempty square matrix on a nonempty finite family of diagonal
blocks preserves its normalized row rank. -/
theorem normalizedRowRank_repeatBlock (A : Matrix n n K) :
    normalizedRowRank (repeatBlock (o := o) A) = normalizedRowRank A := by
  rw [normalizedRowRank, normalizedRowRank, rowRank_repeatBlock,
    Fintype.card_prod]
  simp only [Nat.cast_mul]
  have hn : (Fintype.card n : ℝ) ≠ 0 := card_cast_pos.ne'
  have ho_pos : (0 : ℝ) < Fintype.card o := by
    exact_mod_cast Fintype.card_pos
  have ho : (Fintype.card o : ℝ) ≠ 0 := ho_pos.ne'
  field_simp

end PositiveSize

end Matrix
