/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import GeneralLinearGroups.RelativeElementary
public import GeneralLinearGroups.ElementaryWhitehead

/-!
# Finite relative Whitehead block units

Over an arbitrary ring, ideal-valued upper and lower blocks lie in the
relative elementary group after doubling. A five-factor identity puts the
Whitehead diagonal of a congruence unit in the same relative group. The
relative subgroup is the existing normal closure inside the elementary group.
-/

set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : Type v} [Ring R]

/-- An ideal-valued upper block unit belongs to the doubled relative elementary
subgroup; this also holds for an empty index type. -/
theorem upperUnit_mem_relativeElementarySubgroup (I : TwoSidedIdeal R)
    (a : Matrix ι ι R) (ha : ∀ i j, a i j ∈ I) :
    (⟨upperUnit a, upperUnit_mem_elementarySubgroup a⟩ :
      elementarySubgroup (ι ⊕ ι) R) ∈ relativeElementarySubgroup I := by
  let b : Matrix ι ι I := fun i j => ⟨a i j, ha i j⟩
  have h (b : Matrix ι ι I) :
      (⟨upperUnit (fun i j => (b i j : R)),
        upperUnit_mem_elementarySubgroup _⟩ : elementarySubgroup (ι ⊕ ι) R) ∈
        relativeElementarySubgroup I := by
    induction b using Matrix.induction_on' with
    | h_zero =>
        convert (relativeElementarySubgroup (ι := ι ⊕ ι) I).one_mem using 1
        apply Subtype.ext
        exact upperUnit_zero
    | h_add p q hp hq =>
        have heq : (fun i j => (((p + q) i j : I) : R)) =
            (fun i j => (p i j : R)) + (fun i j => (q i j : R)) := by
          ext i j
          rfl
        convert (relativeElementarySubgroup I).mul_mem hp hq using 1
        apply Subtype.ext
        change upperUnit (fun i j => (((p + q) i j : I) : R)) =
          upperUnit (fun i j => (p i j : R)) * upperUnit (fun i j => (q i j : R))
        rw [heq]
        exact upperUnit_add _ _
    | h_std_basis i j c =>
        have heq : (fun row col => ((Matrix.single i j c row col : I) : R)) =
            Matrix.single i j (c : R) := by
          ext row col
          simp only [Matrix.single_apply]
          split_ifs <;> rfl
        convert elementaryUnit_mem_relativeElementarySubgroup I
          (Sum.inl i) (Sum.inr j) (by simp) c c.property using 1
        apply Subtype.ext
        simpa only [heq] using upperUnit_single i j (c : R)
  simpa only [b] using h b

/-- An ideal-valued lower block unit belongs to the doubled relative elementary
subgroup. Its lower-left block is `-a`, so its elementary generators use `-a i j`. -/
theorem lowerUnit_mem_relativeElementarySubgroup (I : TwoSidedIdeal R)
    (a : Matrix ι ι R) (ha : ∀ i j, a i j ∈ I) :
    (⟨lowerUnit a, lowerUnit_mem_elementarySubgroup a⟩ :
      elementarySubgroup (ι ⊕ ι) R) ∈ relativeElementarySubgroup I := by
  let b : Matrix ι ι I := fun i j => ⟨a i j, ha i j⟩
  have h (b : Matrix ι ι I) :
      (⟨lowerUnit (fun i j => (b i j : R)),
        lowerUnit_mem_elementarySubgroup _⟩ : elementarySubgroup (ι ⊕ ι) R) ∈
        relativeElementarySubgroup I := by
    induction b using Matrix.induction_on' with
    | h_zero =>
        convert (relativeElementarySubgroup (ι := ι ⊕ ι) I).one_mem using 1
        apply Subtype.ext
        exact lowerUnit_zero
    | h_add p q hp hq =>
        have heq : (fun i j => (((p + q) i j : I) : R)) =
            (fun i j => (p i j : R)) + (fun i j => (q i j : R)) := by
          ext i j
          rfl
        convert (relativeElementarySubgroup I).mul_mem hp hq using 1
        apply Subtype.ext
        change lowerUnit (fun i j => (((p + q) i j : I) : R)) =
          lowerUnit (fun i j => (p i j : R)) * lowerUnit (fun i j => (q i j : R))
        rw [heq]
        exact lowerUnit_add _ _
    | h_std_basis i j c =>
        have heq : (fun row col => ((Matrix.single i j c row col : I) : R)) =
            Matrix.single i j (c : R) := by
          ext row col
          simp only [Matrix.single_apply]
          split_ifs <;> rfl
        convert elementaryUnit_mem_relativeElementarySubgroup I
          (Sum.inr i) (Sum.inl j) (by simp) (-(c : R)) (I.neg_mem c.property) using 1
        apply Subtype.ext
        simpa only [heq] using lowerUnit_single i j (c : R)
  simpa only [b] using h b

/-- The native five-factor block identity; `lowerUnit b` has lower-left block
`-b`. No ideal hypothesis is needed. -/
theorem blockDiagonalUnit_eq_five (g : GL ι R) :
    blockDiagonalUnit g =
      upperUnit (1 : Matrix ι ι R) *
        lowerUnit (-((g : Matrix ι ι R) - 1)) *
          upperUnit (-1 : Matrix ι ι R) *
            upperUnit ((((g⁻¹ : GL ι R) : Matrix ι ι R) *
              ((g : Matrix ι ι R) - 1))) *
              lowerUnit ((g : Matrix ι ι R) * ((g : Matrix ι ι R) - 1)) := by
  apply Units.ext
  simp only [blockDiagonalUnit, upperUnit, lowerUnit, neg_sub, neg_neg, Matrix.mul_sub,
    Units.inv_mul, mul_one, Units.val_mul, Matrix.fromBlocks_multiply, one_mul,
    add_sub_cancel, mul_zero, zero_add, add_zero, mul_neg, Units.mul_inv,
    sub_add_add_cancel, add_neg_cancel, Matrix.sub_mul, zero_mul,
    Matrix.fromBlocks_inj, true_and]
  constructor
  · have hq : (g : Matrix ι ι R) - 1 -
        (1 - ((g⁻¹ : GL ι R) : Matrix ι ι R)) + (1 - (g : Matrix ι ι R) + 1) =
        ((g⁻¹ : GL ι R) : Matrix ι ι R) := by abel
    rw [hq, ← Matrix.mul_assoc]
    have hinv : ((g⁻¹ : GL ι R) : Matrix ι ι R) * (g : Matrix ι ι R) = 1 :=
      Units.inv_mul _
    rw [hinv, one_mul]
    abel
  · abel

/-- The Whitehead diagonal of a congruence unit is relative elementary after
doubling, with conjugation only inside the existing elementary subgroup. -/
theorem blockDiagonalUnit_mem_relativeElementarySubgroup (I : TwoSidedIdeal R)
    (g : congruenceSubgroup (n := ι) I) :
    (⟨blockDiagonalUnit g.1, blockDiagonalUnit_mem_elementarySubgroup g.1⟩ :
      elementarySubgroup (ι ⊕ ι) R) ∈ relativeElementarySubgroup I := by
  let a : Matrix ι ι R := (g.1 : Matrix ι ι R) - 1
  let q : Matrix ι ι R := ((g.1⁻¹ : GL ι R) : Matrix ι ι R)
  have ha (i j : ι) : a i j ∈ I := by
    simpa only [a, Matrix.sub_apply] using congruenceSubgroup_entry_sub_mem I g i j
  have hleft (m : Matrix ι ι R) (i j : ι) : (m * a) i j ∈ I := by
    rw [Matrix.mul_apply]
    change (∑ k, m i k * a k j) ∈ I.asIdeal
    apply I.asIdeal.sum_mem
    intro k _
    exact I.mul_mem_left (m i k) (a k j) (ha k j)
  let upper : elementarySubgroup (ι ⊕ ι) R :=
    ⟨upperUnit (1 : Matrix ι ι R), upperUnit_mem_elementarySubgroup _⟩
  let lower : elementarySubgroup (ι ⊕ ι) R :=
    ⟨lowerUnit (-a), lowerUnit_mem_elementarySubgroup _⟩
  let upperInv : elementarySubgroup (ι ⊕ ι) R :=
    ⟨upperUnit (-1 : Matrix ι ι R), upperUnit_mem_elementarySubgroup _⟩
  let upperQa : elementarySubgroup (ι ⊕ ι) R :=
    ⟨upperUnit (q * a), upperUnit_mem_elementarySubgroup _⟩
  let lowerGa : elementarySubgroup (ι ⊕ ι) R :=
    ⟨lowerUnit ((g.1 : Matrix ι ι R) * a), lowerUnit_mem_elementarySubgroup _⟩
  have hLower : lower ∈ relativeElementarySubgroup I := by
    apply lowerUnit_mem_relativeElementarySubgroup I (-a)
    intro i j
    simpa only [Matrix.neg_apply] using I.neg_mem (ha i j)
  have hUpperQa : upperQa ∈ relativeElementarySubgroup I :=
    upperUnit_mem_relativeElementarySubgroup I (q * a) (hleft q)
  have hLowerGa : lowerGa ∈ relativeElementarySubgroup I :=
    lowerUnit_mem_relativeElementarySubgroup I ((g.1 : Matrix ι ι R) * a)
      (hleft (g.1 : Matrix ι ι R))
  have hUpperInv : upperInv = upper⁻¹ := by
    apply Subtype.ext
    change upperUnit (-1 : Matrix ι ι R) = (upperUnit (1 : Matrix ι ι R))⁻¹
    apply Units.ext
    simp [upperUnit]
  have hConj : upper * lower * upperInv ∈ relativeElementarySubgroup I := by
    rw [hUpperInv]
    exact (inferInstance : (relativeElementarySubgroup (ι := ι ⊕ ι) I).Normal).conj_mem
      lower hLower upper
  have hFactor :
      (⟨blockDiagonalUnit g.1, blockDiagonalUnit_mem_elementarySubgroup g.1⟩ :
        elementarySubgroup (ι ⊕ ι) R) =
          upper * lower * upperInv * upperQa * lowerGa := by
    apply Subtype.ext
    change blockDiagonalUnit g.1 =
      upperUnit (1 : Matrix ι ι R) * lowerUnit (-a) * upperUnit (-1) *
        upperUnit (q * a) * lowerUnit ((g.1 : Matrix ι ι R) * a)
    exact blockDiagonalUnit_eq_five g.1
  rw [hFactor]
  exact (relativeElementarySubgroup I).mul_mem
    ((relativeElementarySubgroup I).mul_mem hConj hUpperQa) hLowerGa

end Matrix.GeneralLinearGroup
