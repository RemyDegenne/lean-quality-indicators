/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RectangularBlockUnits
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Unit-pivot elementary diagonalization

The leading principal minor of order `k` uses the order-preserving inclusion
`Fin k → Fin n`. Reindexing preserves the existing elementary subgroup for
arbitrary finite index types. These interfaces work over rings with zero divisors,
including the zero ring.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uκ uR

variable {ι : Type uι} {κ : Type uκ} {R : Type uR}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Ring R]

/-- Reindexing an elementary unit reindexes its two distinct indices. -/
theorem reindexEquiv_elementaryUnit (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    reindexEquiv R e (elementaryUnit i j hij a) =
      elementaryUnit (e i) (e j) (fun h => hij (e.injective h)) a := by
  apply Units.ext
  ext row col
  simp [Matrix.single_apply, Matrix.one_apply, Matrix.add_apply,
    e.eq_symm_apply]

/-- An equivalence of finite index types preserves the algebraic elementary subgroup. -/
theorem reindexEquiv_mem_elementarySubgroup (e : ι ≃ κ)
    {g : GL ι R} (hg : g ∈ elementarySubgroup ι R) :
    reindexEquiv R e g ∈ elementarySubgroup κ R := by
  have hmap : (elementarySubgroup ι R).map (reindexEquiv R e).toMonoidHom ≤
      elementarySubgroup κ R := by
    apply Subgroup.map_le_iff_le_comap.mpr
    change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, j, hij, a, rfl⟩
    change reindexEquiv R e (elementaryUnit i j hij a) ∈ elementarySubgroup κ R
    rw [reindexEquiv_elementaryUnit]
    exact elementaryUnit_mem (e i) (e j) (fun h => hij (e.injective h)) a
  exact hmap (Subgroup.mem_map_of_mem _ hg)

/-- Reindexing restricts to a homomorphism of the existing elementary subgroups. -/
def reindexElementarySubgroup (e : ι ≃ κ) :
    elementarySubgroup ι R →* elementarySubgroup κ R where
  toFun g := ⟨reindexEquiv R e g.1, reindexEquiv_mem_elementarySubgroup e g.2⟩
  map_one' := Subtype.ext (map_one (reindexEquiv R e).toMonoidHom)
  map_mul' _ _ := Subtype.ext (map_mul (reindexEquiv R e).toMonoidHom _ _)

@[simp]
theorem reindexElementarySubgroup_coe (e : ι ≃ κ) (g : elementarySubgroup ι R) :
    ((reindexElementarySubgroup e g : elementarySubgroup κ R) : GL κ R) =
      reindexEquiv R e g := rfl

/-- An elementary lower block shear obtained by exchanging the two blocks of
the published upper block shear. -/
def rectangularLowerUnit {X : Type uι} {Y : Type uκ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (C : Matrix Y X R) : GL (X ⊕ Y) R :=
  reindexEquiv R (Equiv.sumComm Y X) (rectangularUpperUnit C)

@[simp]
theorem rectangularLowerUnit_val {X : Type uι} {Y : Type uκ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (C : Matrix Y X R) :
    (rectangularLowerUnit C : Matrix (X ⊕ Y) (X ⊕ Y) R) =
      Matrix.fromBlocks 1 0 C 1 := by
  ext row col
  rcases row with row | row <;> rcases col with col | col <;>
    simp [rectangularLowerUnit, rectangularUpperUnit_val, Matrix.one_apply]

/-- The inverse lower block shear has lower block `-C`. -/
@[simp]
theorem rectangularLowerUnit_inv {X : Type uι} {Y : Type uκ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (C : Matrix Y X R) :
    (rectangularLowerUnit C)⁻¹ = rectangularLowerUnit (-C) := by
  change (reindexEquiv R (Equiv.sumComm Y X) (rectangularUpperUnit C))⁻¹ =
    reindexEquiv R (Equiv.sumComm Y X) (rectangularUpperUnit (-C))
  rw [← (reindexEquiv R (Equiv.sumComm Y X)).map_inv (rectangularUpperUnit C),
    rectangularUpperUnit_inv]

theorem rectangularLowerUnit_mem_elementarySubgroup {X : Type uι} {Y : Type uκ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (C : Matrix Y X R) :
    rectangularLowerUnit C ∈ elementarySubgroup (X ⊕ Y) R :=
  reindexEquiv_mem_elementarySubgroup (Equiv.sumComm Y X)
    (rectangularUpperUnit_mem_elementarySubgroup C)

/-- Stabilize an elementary factor in the trailing rather than the first block. -/
def trailingElementary {X : Type uι} {Y : Type uκ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    elementarySubgroup Y R →* elementarySubgroup (X ⊕ Y) R :=
  (reindexElementarySubgroup (Equiv.sumComm Y X)).comp
    (stabilizeElementarySubgroup (Y := X))

@[simp]
theorem trailingElementary_val {X : Type uι} {Y : Type uκ}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (g : elementarySubgroup Y R) :
    (((trailingElementary (X := X) g : elementarySubgroup (X ⊕ Y) R) :
      GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) =
        Matrix.fromBlocks 1 0 0 ((g : GL Y R) : Matrix Y Y R) := by
  simpa [trailingElementary] using
    (diagonalPairUnit_val (1 : GL X R) (g : GL Y R))

end Matrix.GeneralLinearGroup

namespace Matrix

universe uX uY uR

section Ring

variable {R : Type uR} [Ring R]

/-- Clearing the off-diagonal blocks at a unit pivot uses two factors in the
existing elementary subgroup, without requiring the Schur residual to be invertible. -/
theorem fromBlocks_elementary_reduce {X : Type uX} {Y : Type uY}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (A : Matrix X X R) (B : Matrix X Y R) (C : Matrix Y X R) (D : Matrix Y Y R)
    [Invertible A] :
    ∃ L Q : GeneralLinearGroup.elementarySubgroup (X ⊕ Y) R,
      ((L : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) *
          Matrix.fromBlocks A B C D *
        ((Q : GL (X ⊕ Y) R) : Matrix (X ⊕ Y) (X ⊕ Y) R) =
          Matrix.fromBlocks A 0 0 (D - C * ⅟A * B) := by
  let L : GeneralLinearGroup.elementarySubgroup (X ⊕ Y) R :=
    ⟨GeneralLinearGroup.rectangularLowerUnit (-(C * ⅟A)),
      GeneralLinearGroup.rectangularLowerUnit_mem_elementarySubgroup _⟩
  let Q : GeneralLinearGroup.elementarySubgroup (X ⊕ Y) R :=
    ⟨GeneralLinearGroup.rectangularUpperUnit (-(⅟A * B)),
      GeneralLinearGroup.rectangularUpperUnit_mem_elementarySubgroup _⟩
  refine ⟨L, Q, ?_⟩
  change (GeneralLinearGroup.rectangularLowerUnit (-(C * ⅟A)) :
      Matrix (X ⊕ Y) (X ⊕ Y) R) * Matrix.fromBlocks A B C D *
        (GeneralLinearGroup.rectangularUpperUnit (-(⅟A * B)) :
          Matrix (X ⊕ Y) (X ⊕ Y) R) = _
  rw [GeneralLinearGroup.rectangularLowerUnit_val,
    GeneralLinearGroup.rectangularUpperUnit_val]
  simp [Matrix.fromBlocks_multiply, Matrix.mul_assoc, Matrix.mul_neg,
    Matrix.neg_mul, sub_eq_add_neg, add_comm]
  simpa only [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul] using (add_neg_cancel B)

end Ring

variable {R : Type uR} [CommRing R]

/-- The northwest `k × k` principal determinant, with its ordered `Fin` inclusion. -/
def leadingPrincipalMinor {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (k : ℕ) (hk : k ≤ n) : R :=
  (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det

@[simp]
theorem leadingPrincipalMinor_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    leadingPrincipalMinor M 0 (Nat.zero_le n) = 1 := by
  exact det_isEmpty

@[simp]
theorem leadingPrincipalMinor_full {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    leadingPrincipalMinor M n le_rfl = M.det := by
  simp [leadingPrincipalMinor]

/-- Every element of the algebraic elementary subgroup has determinant one. -/
theorem det_elementarySubgroup_eq_one {n : Type*}
    [Fintype n] [DecidableEq n]
    (g : GeneralLinearGroup.elementarySubgroup n R) :
    GeneralLinearGroup.det (g : GL n R) = 1 := by
  have hker : GeneralLinearGroup.elementarySubgroup n R ≤
      (GeneralLinearGroup.det (n := n) (R := R)).ker := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, j, hij, a, rfl⟩
    apply Units.ext
    simpa [GeneralLinearGroup.elementaryUnit_val, Matrix.transvection] using
      (Matrix.det_transvection_of_ne i j hij a)
  exact (MonoidHom.mem_ker.mp (hker g.property))

/-- Split the first index from the remaining indices, without changing their order. -/
def firstRestEquiv (n : ℕ) : Fin (n + 1) ≃ Fin 1 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 1)).trans finSumFinEquiv.symm

@[simp]
theorem firstRestEquiv_symm_inl (n : ℕ) (i : Fin 1) :
    (firstRestEquiv n).symm (Sum.inl i) = 0 := by
  apply Fin.ext
  simp [firstRestEquiv]

@[simp]
theorem firstRestEquiv_symm_inr (n : ℕ) (i : Fin n) :
    (firstRestEquiv n).symm (Sum.inr i) = i.succ := by
  apply Fin.ext
  simp [firstRestEquiv]

@[simp]
theorem firstRestEquiv_zero (n : ℕ) : firstRestEquiv n 0 = Sum.inl 0 := by
  apply (firstRestEquiv n).symm.injective
  simp

@[simp]
theorem firstRestEquiv_succ (n : ℕ) (i : Fin n) :
    firstRestEquiv n i.succ = Sum.inr i := by
  apply (firstRestEquiv n).symm.injective
  simp

/-- The ordered first-coordinate block decomposition. -/
def firstRestBlock {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R :=
  M.submatrix (firstRestEquiv n).symm (firstRestEquiv n).symm

@[simp]
theorem firstRestBlock_pivot {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (firstRestBlock M).toBlocks₁₁.det = leadingPrincipalMinor M 1 (Nat.le_add_left 1 n) := by
  simp [leadingPrincipalMinor, firstRestBlock,
    Matrix.toBlocks₁₁, Matrix.submatrix_apply]

omit [CommRing R] in
/-- Restricting an ordered first-coordinate block decomposition to an initial segment
restricts only its trailing rows and columns. -/
theorem firstRestBlock_prefix {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (j : ℕ) (hj : j ≤ n) :
    ((M.submatrix (Fin.castLE (Nat.succ_le_succ hj))
      (Fin.castLE (Nat.succ_le_succ hj))).submatrix
        (firstRestEquiv j).symm (firstRestEquiv j).symm) =
      Matrix.fromBlocks (firstRestBlock M).toBlocks₁₁
        ((firstRestBlock M).toBlocks₁₂.submatrix id (Fin.castLE hj))
        ((firstRestBlock M).toBlocks₂₁.submatrix (Fin.castLE hj) id)
        ((firstRestBlock M).toBlocks₂₂.submatrix (Fin.castLE hj) (Fin.castLE hj)) := by
  ext row col
  rcases row with row | row <;> rcases col with col | col <;>
    simp [firstRestBlock, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.submatrix_apply]

set_option linter.style.haveILetI false in
/-- The Schur residual retains every leading minor, up to the unit pivot.
The middle multiplication index is `Fin 1` even when the outside indices shrink. -/
theorem leadingPrincipalMinor_schur {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : IsUnit (leadingPrincipalMinor M 1 (Nat.le_add_left 1 n)))
    (j : ℕ) (hj : j ≤ n) :
    leadingPrincipalMinor M (j + 1) (Nat.succ_le_succ hj) =
      (firstRestBlock M).toBlocks₁₁.det *
        leadingPrincipalMinor
          ((firstRestBlock M).toBlocks₂₂ -
            (firstRestBlock M).toBlocks₂₁ *
              ((firstRestBlock M).toBlocks₁₁)⁻¹ *
                (firstRestBlock M).toBlocks₁₂) j hj := by
  let T := firstRestBlock M
  let A := T.toBlocks₁₁
  let B := T.toBlocks₁₂
  let C := T.toBlocks₂₁
  let D := T.toBlocks₂₂
  have hA : IsUnit A.det := by
    change IsUnit (firstRestBlock M).toBlocks₁₁.det
    rwa [firstRestBlock_pivot]
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  let e := Fin.castLE hj
  have hschur : (D - C * ⅟A * B).submatrix e e =
      D.submatrix e e - (C.submatrix e id) * ⅟A * (B.submatrix id e) := by
    ext row col
    simp [Matrix.mul_apply]
  calc
    leadingPrincipalMinor M (j + 1) (Nat.succ_le_succ hj) =
        ((M.submatrix (Fin.castLE (Nat.succ_le_succ hj))
            (Fin.castLE (Nat.succ_le_succ hj))).submatrix
          (firstRestEquiv j).symm (firstRestEquiv j).symm).det := by
      exact (Matrix.det_submatrix_equiv_self (firstRestEquiv j).symm _).symm
    _ = (Matrix.fromBlocks A (B.submatrix id e) (C.submatrix e id)
          (D.submatrix e e)).det := by
      rw [firstRestBlock_prefix]
    _ = A.det * (D.submatrix e e - (C.submatrix e id) * ⅟A *
          (B.submatrix id e)).det := Matrix.det_fromBlocks₁₁ _ _ _ _
    _ = A.det * ((D - C * ⅟A * B).submatrix e e).det := by rw [hschur]
    _ = (firstRestBlock M).toBlocks₁₁.det *
          leadingPrincipalMinor
            ((firstRestBlock M).toBlocks₂₂ -
              (firstRestBlock M).toBlocks₂₁ *
                ((firstRestBlock M).toBlocks₁₁)⁻¹ *
                  (firstRestBlock M).toBlocks₁₂) j hj := by
      rw [Matrix.invOf_eq_nonsing_inv]
      rfl

/-- A unit first pivot and an elementary diagonalization of its Schur residual
give an elementary diagonalization of the full matrix. -/
theorem exists_elementary_diagonalization_of_unit_pivot {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hA : IsUnit (firstRestBlock M).toBlocks₁₁.det)
    (l q : GeneralLinearGroup.elementarySubgroup (Fin n) R) (d : Fin n → Rˣ)
    (hd : ((l : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((firstRestBlock M).toBlocks₂₂ -
        (firstRestBlock M).toBlocks₂₁ *
          (firstRestBlock M).toBlocks₁₁⁻¹ * (firstRestBlock M).toBlocks₁₂) *
      ((q : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        Matrix.diagonal (fun i => (d i : R))) :
    ∃ L Q : GeneralLinearGroup.elementarySubgroup (Fin (n + 1)) R,
      ∃ diagonal : Fin (n + 1) → Rˣ,
        ((L : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * M *
          ((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
            Matrix.diagonal (fun i => (diagonal i : R)) := by
  let T := firstRestBlock M
  let A := T.toBlocks₁₁
  let B := T.toBlocks₁₂
  let C := T.toBlocks₂₁
  let D := T.toBlocks₂₂
  let inverseA : Invertible A := Matrix.invertibleOfIsUnitDet A hA
  let S := D - C * A⁻¹ * B
  have hdS : ((l : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * S *
      ((q : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        Matrix.diagonal (fun i => (d i : R)) := hd
  obtain ⟨l₀, q₀, hreduce⟩ := fromBlocks_elementary_reduce A B C D
  have hreduceT : ((l₀ : GL (Fin 1 ⊕ Fin n) R) :
      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) * T *
      ((q₀ : GL (Fin 1 ⊕ Fin n) R) : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) =
        Matrix.fromBlocks A 0 0 S := by
    simpa only [A, B, C, D, Matrix.fromBlocks_toBlocks,
      Matrix.invOf_eq_nonsing_inv] using hreduce
  let lSum := GeneralLinearGroup.trailingElementary (X := Fin 1) l * l₀
  let qSum := q₀ * GeneralLinearGroup.trailingElementary (X := Fin 1) q
  have hSum : ((lSum : GL (Fin 1 ⊕ Fin n) R) :
      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) * T *
      ((qSum : GL (Fin 1 ⊕ Fin n) R) : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) =
        Matrix.fromBlocks A 0 0 (Matrix.diagonal (fun i => (d i : R))) := by
    calc
      ((lSum : GL (Fin 1 ⊕ Fin n) R) :
          Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) * T *
          ((qSum : GL (Fin 1 ⊕ Fin n) R) :
            Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) =
            ((GeneralLinearGroup.trailingElementary (X := Fin 1) l :
                GL (Fin 1 ⊕ Fin n) R) : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) *
              (((l₀ : GL (Fin 1 ⊕ Fin n) R) :
                  Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) * T *
                ((q₀ : GL (Fin 1 ⊕ Fin n) R) :
                  Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R)) *
                ((GeneralLinearGroup.trailingElementary (X := Fin 1) q :
                    GL (Fin 1 ⊕ Fin n) R) :
                      Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) := by
              simp [lSum, qSum, Matrix.mul_assoc]
      _ = _ := by rw [hreduceT]
      _ = Matrix.fromBlocks A 0 0 (Matrix.diagonal (fun i => (d i : R))) := by
            simp [GeneralLinearGroup.trailingElementary_val,
              Matrix.fromBlocks_multiply, hdS]
  let L := GeneralLinearGroup.reindexElementarySubgroup (firstRestEquiv n).symm lSum
  let Q := GeneralLinearGroup.reindexElementarySubgroup (firstRestEquiv n).symm qSum
  let pivot : Rˣ := hA.unit
  let diagonalUnits : Fin (n + 1) → Rˣ := Fin.cases pivot d
  have hpivot : A 0 0 = (pivot : R) := by
    simpa only [Matrix.det_fin_one, pivot] using hA.unit_spec.symm
  have hdiag :
      (Matrix.fromBlocks A 0 0 (Matrix.diagonal (fun i => (d i : R)))).submatrix
          (firstRestEquiv n) (firstRestEquiv n) =
            Matrix.diagonal (fun i => (diagonalUnits i : R)) := by
    ext i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => simpa [diagonalUnits] using hpivot
        | succ j =>
            have hne : (0 : Fin (n + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
            simp [diagonalUnits, hne]
    | succ i =>
        cases j using Fin.cases with
        | zero => simp [diagonalUnits]
        | succ j => simp [diagonalUnits, Matrix.diagonal_apply]
  have hM : T.submatrix (firstRestEquiv n) (firstRestEquiv n) = M := by
    ext i j
    simp [T, firstRestBlock]
  have hcoe (g : GeneralLinearGroup.elementarySubgroup (Fin 1 ⊕ Fin n) R) :
      ((GeneralLinearGroup.reindexElementarySubgroup
          (firstRestEquiv n).symm g : GL (Fin (n + 1)) R) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        ((g : GL (Fin 1 ⊕ Fin n) R) :
          Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R).submatrix
            (firstRestEquiv n) (firstRestEquiv n) := by
    ext i j
    simp only [GeneralLinearGroup.reindexElementarySubgroup_coe,
      GeneralLinearGroup.reindexEquiv_apply, Matrix.submatrix_apply,
      Equiv.symm_symm]
  have h' := congrArg
    (fun P : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R =>
      P.submatrix (firstRestEquiv n) (firstRestEquiv n)) hSum
  have hfact : ((L : GL (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) * M *
        ((Q : GL (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) =
        (((lSum : GL (Fin 1 ⊕ Fin n) R) :
            Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R) * T *
          ((qSum : GL (Fin 1 ⊕ Fin n) R) :
            Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) R)).submatrix
              (firstRestEquiv n) (firstRestEquiv n) := by
    rw [hcoe lSum, hcoe qSum, ← hM]
    simp only [Matrix.submatrix_mul_equiv]
  exact ⟨L, Q, diagonalUnits, hfact.trans (h'.trans hdiag)⟩

set_option linter.style.haveILetI false in
/-- Unit leading principal minors permit two-sided diagonalization using only
the existing elementary subgroup. No domain, field or determinant-one hypothesis
is needed. -/
theorem exists_elementary_diagonalization_of_unit_leadingPrincipalMinors :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), 0 < k → IsUnit (leadingPrincipalMinor M k hk)) →
        ∃ L Q : GeneralLinearGroup.elementarySubgroup (Fin n) R,
          ∃ d : Fin n → Rˣ,
            ((L : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * M *
                ((Q : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
                  Matrix.diagonal (fun i => (d i : R)) := by
  intro n
  induction n with
  | zero =>
      intro M _
      refine ⟨1, 1, (fun i => i.elim0), ?_⟩
      ext i
      exact i.elim0
  | succ n ih =>
      intro M h
      have hp : IsUnit (leadingPrincipalMinor M 1 (Nat.le_add_left 1 n)) :=
        h 1 (Nat.le_add_left 1 n) (by omega)
      let T := firstRestBlock M
      let A := T.toBlocks₁₁
      let B := T.toBlocks₁₂
      let C := T.toBlocks₂₁
      let D := T.toBlocks₂₂
      have hA : IsUnit A.det := by
        change IsUnit (firstRestBlock M).toBlocks₁₁.det
        rwa [firstRestBlock_pivot]
      haveI : Invertible A := Matrix.invertibleOfIsUnitDet A hA
      let S := D - C * A⁻¹ * B
      have hS : ∀ (k : ℕ) (hk : k ≤ n), 0 < k →
          IsUnit (leadingPrincipalMinor S k hk) := by
        intro k hk hkpos
        have hmk := h (k + 1) (Nat.succ_le_succ hk) (Nat.zero_lt_succ k)
        rw [leadingPrincipalMinor_schur M hp k hk] at hmk
        exact (IsUnit.mul_iff.mp hmk).2
      obtain ⟨l, q, d, hd⟩ := ih S hS
      exact exists_elementary_diagonalization_of_unit_pivot M hA l q d hd

/-- Read the diagonal entries as a determinant product without an SL assumption. -/
theorem det_eq_prod_of_elementary_diagonalization {n : ℕ}
    {M : Matrix (Fin n) (Fin n) R}
    {L Q : GeneralLinearGroup.elementarySubgroup (Fin n) R}
    {d : Fin n → Rˣ}
    (h : ((L : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * M *
      ((Q : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        Matrix.diagonal (fun i => (d i : R))) :
    M.det = ∏ i, (d i : R) := by
  have hL : ((L : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det = 1 := by
    exact congrArg Units.val (det_elementarySubgroup_eq_one L)
  have hQ : ((Q : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det = 1 := by
    exact congrArg Units.val (det_elementarySubgroup_eq_one Q)
  have hd := congrArg Matrix.det h
  simpa [Matrix.det_mul, Matrix.det_diagonal, hL, hQ] using hd

end Matrix
