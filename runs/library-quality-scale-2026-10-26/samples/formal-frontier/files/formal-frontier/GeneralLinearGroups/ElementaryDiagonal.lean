/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.UnitPivotDiagonalization
public import GeneralLinearGroups.ElementaryWhitehead

/-!
# Elementary product-one diagonals

A diagonal of units with product one is elementary over any commutative ring.
The proof uses the published Whitehead inverse pair and stabilization of the
existing algebraic elementary subgroup.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uR

variable {R : Type uR} [CommRing R]

/-- The invertible diagonal matrix associated to a family of units. -/
def diagonalUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → Rˣ) : GL ι R where
  val := Matrix.diagonal (fun i => (d i : R))
  inv := Matrix.diagonal (fun i => ((d i)⁻¹).val)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Units.mul_inv (d i)
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact Units.inv_mul (d i)

@[simp]
theorem diagonalUnit_val {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → Rˣ) :
    ((diagonalUnit d : GL ι R) : Matrix ι ι R) =
      Matrix.diagonal (fun i => (d i : R)) := rfl

@[simp]
theorem diagonalUnit_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    diagonalUnit (fun _ : ι => (1 : Rˣ)) = 1 := by
  apply Units.ext
  simp

@[simp]
theorem diagonalUnit_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d e : ι → Rˣ) :
    diagonalUnit (fun i => d i * e i) = diagonalUnit d * diagonalUnit e := by
  apply Units.ext
  simp [Matrix.diagonal_mul_diagonal]

private theorem diagonalUnit_reindex {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (d : ι → Rˣ) :
    reindexEquiv R e (diagonalUnit d) = diagonalUnit (d ∘ e.symm) := by
  apply Units.ext
  ext i j
  simp [reindexEquiv_apply, Matrix.diagonal_apply, e.symm.injective.eq_iff]

private theorem diagonalUnit_stabilize_mem {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (d : X → Rˣ) (hd : diagonalUnit d ∈ elementarySubgroup X R) :
    diagonalUnit (Sum.elim d (fun _ : Y => 1)) ∈ elementarySubgroup (X ⊕ Y) R := by
  let g : elementarySubgroup X R := ⟨diagonalUnit d, hd⟩
  have h : ((stabilizeElementarySubgroup (Y := Y) g : GL (X ⊕ Y) R)) =
      diagonalUnit (Sum.elim d (fun _ : Y => 1)) := by
    apply Units.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [g, stabilizeElementarySubgroup_coe, Matrix.diagonal_apply]
    simp [Matrix.one_apply]
  rw [← h]
  exact (stabilizeElementarySubgroup (Y := Y) g).2

private theorem diagonalUnit_trailing_mem {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (d : Y → Rˣ) (hd : diagonalUnit d ∈ elementarySubgroup Y R) :
    diagonalUnit (Sum.elim (fun _ : X => 1) d) ∈ elementarySubgroup (X ⊕ Y) R := by
  let g : elementarySubgroup Y R := ⟨diagonalUnit d, hd⟩
  have h : ((trailingElementary (X := X) g : GL (X ⊕ Y) R)) =
      diagonalUnit (Sum.elim (fun _ : X => 1) d) := by
    apply Units.ext
    rw [trailingElementary_val]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [g, Matrix.diagonal_apply]
    simp [Matrix.one_apply]
  rw [← h]
  exact (trailingElementary (X := X) g).2

private theorem diagonalUnit_pair_mem (a : Rˣ) :
    diagonalUnit (Fin.cases a (fun _ : Fin 1 => a⁻¹)) ∈
      elementarySubgroup (Fin 2) R := by
  let scalar : GL (Fin 1) R := scalar (Fin 1) a
  have hs : scalar = diagonalUnit (fun _ : Fin 1 => a) := by
    apply Units.ext
    ext i j
    simp [scalar, Matrix.diagonal_apply]
  have hi : scalar⁻¹ = diagonalUnit (fun _ : Fin 1 => a⁻¹) := by
    rw [hs]
    apply Units.ext
    rfl
  have hp : blockDiagonalUnit scalar =
      diagonalUnit (Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => a⁻¹)) := by
    rw [← diagonalPairUnit_inv_pair, hi, hs]
    apply Units.ext
    rw [diagonalPairUnit_val]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.diagonal_apply]
  have hm := reindexEquiv_mem_elementarySubgroup
    (Matrix.firstRestEquiv 1).symm (blockDiagonalUnit_mem_elementarySubgroup scalar)
  rw [hp, diagonalUnit_reindex] at hm
  convert hm using 1
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [Matrix.firstRestEquiv_zero]
  | succ i => simp [Matrix.firstRestEquiv_succ]

private def firstTwoRestEquiv (n : ℕ) : Fin (n + 2) ≃ Fin 2 ⊕ Fin n :=
  (finCongr (Nat.add_comm n 2)).trans finSumFinEquiv.symm

private theorem firstTwoRestEquiv_zero (n : ℕ) :
    firstTwoRestEquiv n 0 = Sum.inl 0 := by
  change (finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2 + n)).symm
    (finCongr (Nat.add_comm n 2) (0 : Fin (n + 2))) = Sum.inl 0
  rw [show finCongr (Nat.add_comm n 2) (0 : Fin (n + 2)) =
      Fin.castAdd n (0 : Fin 2) from by apply Fin.ext; rfl,
    finSumFinEquiv_symm_apply_castAdd]

private theorem firstTwoRestEquiv_one (n : ℕ) :
    firstTwoRestEquiv n 1 = Sum.inl 1 := by
  change (finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2 + n)).symm
    (finCongr (Nat.add_comm n 2) (1 : Fin (n + 2))) = Sum.inl 1
  rw [show finCongr (Nat.add_comm n 2) (1 : Fin (n + 2)) =
      Fin.castAdd n (1 : Fin 2) from by apply Fin.ext; rfl,
    finSumFinEquiv_symm_apply_castAdd]

private theorem firstTwoRestEquiv_succ_succ (n : ℕ) (i : Fin n) :
    firstTwoRestEquiv n i.succ.succ = Sum.inr i := by
  change (finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2 + n)).symm
    (finCongr (Nat.add_comm n 2) i.succ.succ) = Sum.inr i
  rw [show finCongr (Nat.add_comm n 2) i.succ.succ = Fin.natAdd 2 i from by
      apply Fin.ext
      change (i : ℕ) + 1 + 1 = 2 + (i : ℕ)
      omega,
    finSumFinEquiv_symm_apply_natAdd]

private theorem diagonalUnit_firstTwo_mem (n : ℕ) (a : Rˣ) :
    diagonalUnit (Fin.cases a (Fin.cases a⁻¹ (fun _ : Fin n => 1))) ∈
      elementarySubgroup (Fin (n + 2)) R := by
  let pair : Fin 2 → Rˣ := Fin.cases a (fun _ : Fin 1 => a⁻¹)
  have hs : diagonalUnit (Sum.elim pair (fun _ : Fin n => 1)) ∈
      elementarySubgroup (Fin 2 ⊕ Fin n) R :=
    diagonalUnit_stabilize_mem pair (diagonalUnit_pair_mem a)
  have hm := reindexEquiv_mem_elementarySubgroup (firstTwoRestEquiv n).symm hs
  rw [diagonalUnit_reindex] at hm
  convert hm using 1
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp [firstTwoRestEquiv_zero, pair]
  | succ i =>
      cases i using Fin.cases with
      | zero =>
          rw [Fin.succ_zero_eq_one' (n := n + 1)]
          simp only [Nat.reduceAdd, Equiv.symm_symm, Function.comp_apply,
            firstTwoRestEquiv_one, Fin.isValue, Sum.elim_inl, pair]
          rw [← Fin.succ_zero_eq_one' (n := n + 1),
            ← Fin.succ_zero_eq_one' (n := 1)]
          simp only [Fin.cases_succ, Fin.cases_zero]
      | succ i => simp [firstTwoRestEquiv_succ_succ, pair]

/-- A diagonal of units with product one belongs to the algebraic elementary
subgroup, for every size and every commutative ring. -/
theorem diagonalUnit_mem_elementarySubgroup :
    ∀ (n : ℕ) (d : Fin n → Rˣ), (∏ i, d i) = 1 →
      diagonalUnit d ∈ elementarySubgroup (Fin n) R := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro d _
      have h : diagonalUnit d = 1 := by
        apply Units.ext
        ext i
        exact i.elim0
      rw [h]
      exact (elementarySubgroup (Fin 0) R).one_mem
  | one =>
      intro d hd
      have hd0 : d 0 = 1 := by simpa using hd
      have h : d = fun _ => 1 := by
        funext i
        simpa only [Fin.eq_zero i] using hd0
      rw [h, diagonalUnit_one]
      exact (elementarySubgroup (Fin 1) R).one_mem
  | more n _ ih =>
      intro d hd
      let a : Rˣ := d 0
      let rest : Fin (n + 1) → Rˣ :=
        Fin.cases (a * d 1) (fun i : Fin n => d i.succ.succ)
      have hrest : (∏ i, rest i) = 1 := by
        simpa only [Fin.prod_univ_succ, rest, Fin.cases_zero, Fin.cases_succ,
          a, mul_assoc, Fin.succ_zero_eq_one'] using hd
      let pair : Fin (n + 2) → Rˣ :=
        Fin.cases a (Fin.cases a⁻¹ (fun _ : Fin n => 1))
      let tail : Fin (n + 2) → Rˣ := Fin.cases 1 rest
      have hpair : diagonalUnit pair ∈ elementarySubgroup (Fin (n + 2)) R :=
        diagonalUnit_firstTwo_mem n a
      have htail : diagonalUnit tail ∈ elementarySubgroup (Fin (n + 2)) R := by
        have hs : diagonalUnit (Sum.elim (fun _ : Fin 1 => 1) rest) ∈
            elementarySubgroup (Fin 1 ⊕ Fin (n + 1)) R :=
          diagonalUnit_trailing_mem rest (ih rest hrest)
        have hm := reindexEquiv_mem_elementarySubgroup
          (Matrix.firstRestEquiv (n + 1)).symm hs
        rw [diagonalUnit_reindex] at hm
        convert hm using 1
        congr 1
        funext i
        cases i using Fin.cases with
        | zero => simp [tail, Matrix.firstRestEquiv_zero]
        | succ i => simp [tail, Matrix.firstRestEquiv_succ]
      have hfactor : d = fun i => pair i * tail i := by
        funext i
        cases i using Fin.cases with
        | zero => simp [pair, tail, a]
        | succ i =>
            cases i using Fin.cases with
            | zero =>
                rw [Fin.succ_zero_eq_one' (n := n + 1)]
                simp only [pair, a, tail, rest]
                rw [← Fin.succ_zero_eq_one' (n := n + 1)]
                simp only [Fin.cases_succ, Fin.cases_zero]
                group
            | succ i => simp [pair, tail, rest]
      rw [hfactor, diagonalUnit_mul]
      exact (elementarySubgroup (Fin (n + 2)) R).mul_mem hpair htail

/-- A determinant-one invertible matrix whose positive-order leading principal
minors are units is elementary. This is a unit-pivot, not a nonzero-pivot,
criterion and does not assert `SL = E` over an arbitrary ring. -/
theorem mem_elementarySubgroup_of_det_one_of_unit_leadingPrincipalMinors
    {n : ℕ} (g : GL (Fin n) R)
    (hdet : (g : Matrix (Fin n) (Fin n) R).det = 1)
    (hpivots : ∀ (k : ℕ) (hk : k ≤ n), 0 < k →
      IsUnit (Matrix.leadingPrincipalMinor
        (g : Matrix (Fin n) (Fin n) R) k hk)) :
    g ∈ elementarySubgroup (Fin n) R := by
  obtain ⟨L, Q, d, hdiag⟩ :=
    Matrix.exists_elementary_diagonalization_of_unit_leadingPrincipalMinors
      n (g : Matrix (Fin n) (Fin n) R) hpivots
  have hprod : (∏ i, d i) = 1 := by
    apply Units.ext
    simpa using (Matrix.det_eq_prod_of_elementary_diagonalization hdiag).symm.trans hdet
  have hgroup : (L : GL (Fin n) R) * g * (Q : GL (Fin n) R) =
      diagonalUnit d := by
    apply Units.ext
    simpa only [Units.val_mul, diagonalUnit_val] using hdiag
  have hg : g = (L : GL (Fin n) R)⁻¹ * diagonalUnit d * (Q : GL (Fin n) R)⁻¹ := by
    rw [← hgroup]
    group
  rw [hg]
  exact (elementarySubgroup (Fin n) R).mul_mem
    ((elementarySubgroup (Fin n) R).mul_mem
      ((elementarySubgroup (Fin n) R).inv_mem L.property)
      (diagonalUnit_mem_elementarySubgroup n d hprod))
    ((elementarySubgroup (Fin n) R).inv_mem Q.property)

end Matrix.GeneralLinearGroup
