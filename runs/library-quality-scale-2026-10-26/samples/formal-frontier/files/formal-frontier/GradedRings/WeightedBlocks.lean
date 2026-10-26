/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic

@[expose] public section

/-!
# Positive-weight blocks of finitely supported vectors

For a finite family of positive natural weights, the product of the weights times
the maximum of one and the number of indices is a (not necessarily minimal)
weight at which every multiple-weight exponent vector splits into equal blocks.
-/

namespace Finsupp

variable {ι : Type*} [Fintype ι]

/-- A uniform positive block weight for a finite family of positive weights. -/
def weightedBlockSize (w : ι → ℕ) : ℕ :=
  max 1 (Fintype.card ι) * ∏ i, w i

theorem weightedBlockSize_pos (w : ι → ℕ) (hw : ∀ i, 0 < w i) :
    0 < weightedBlockSize w := by
  unfold weightedBlockSize
  exact mul_pos (by omega) (Finset.prod_pos fun i _ => hw i)

private theorem exists_le_weightedBlockSize
    (w : ι → ℕ) (hw : ∀ i, 0 < w i) [Nonempty ι]
    (k : ℕ) (f : ι →₀ ℕ)
    (hf : weight w f = (k + 1) * weightedBlockSize w) :
    ∃ g ≤ f, weight w g = weightedBlockSize w := by
  let P := ∏ i, w i
  let r := Fintype.card ι
  have hP : 0 < P := Finset.prod_pos fun i _ => hw i
  have hr : 0 < r := Fintype.card_pos
  have hD : weightedBlockSize w = r * P := by
    simp [weightedBlockSize, P, r, max_eq_right (by omega : 1 ≤ r)]
  have hdiv (i : ι) : w i ∣ P := Finset.dvd_prod_of_mem w (Finset.mem_univ i)
  have hb (i : ι) : (P / w i) * w i = P := Nat.div_mul_cancel (hdiv i)
  have hbpos (i : ι) : 0 < P / w i := by
    by_contra hn
    have hz : P / w i = 0 := Nat.eq_zero_of_not_pos hn
    have hi := hb i
    rw [hz, zero_mul] at hi
    exact (Nat.ne_of_gt hP) hi.symm
  let q : ι →₀ ℕ := equivFunOnFinite.symm (fun i => f i / (P / w i))
  let t : ι →₀ ℕ := equivFunOnFinite.symm (fun i => f i % (P / w i))
  have hcoord (i : ι) : t i + q i * (P / w i) = f i := by
    change f i % (P / w i) + f i / (P / w i) * (P / w i) = f i
    simpa only [mul_comm] using Nat.mod_add_div (f i) (P / w i)
  have hweight : weight w t + P * q.degree = (k + 1) * (r * P) := by
    calc
      weight w t + P * q.degree = ∑ i, f i * w i := by
        rw [weight_eq_sum, degree_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        simp only [nsmul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        nlinarith [hcoord i, hb i]
      _ = (k + 1) * (r * P) := by
        rw [hD] at hf
        simpa only [weight_eq_sum, nsmul_eq_mul, Nat.cast_id] using hf
  have hsmall : weight w t < r * P := by
    calc
      weight w t = ∑ i, t i * w i := by simp [weight_eq_sum]
      _ < ∑ _i : ι, P := by
        have hlt (i : ι) : t i * w i < P := by
          have ht : t i < P / w i := Nat.mod_lt _ (hbpos i)
          exact (Nat.mul_lt_mul_of_pos_right ht (hw i)).trans_eq (hb i)
        obtain ⟨i⟩ := ‹Nonempty ι›
        exact Finset.sum_lt_sum (fun j _ => (hlt j).le) ⟨i, Finset.mem_univ _, hlt i⟩
      _ = r * P := by simp [r]
  have hRdiv : P ∣ weight w t := by
    have htotal : P ∣ (k + 1) * (r * P) := ⟨(k + 1) * r, by ring⟩
    have hq : P ∣ P * q.degree := by simp
    have hab : P ∣ P * q.degree + weight w t := by
      rw [add_comm, hweight]
      exact htotal
    exact (Nat.dvd_add_iff_right hq).mpr hab
  let m := weight w t / P
  have hR : weight w t = m * P := by
    exact (Nat.div_mul_cancel hRdiv).symm
  have hm : m < r := by
    have := hsmall
    rw [hR] at this
    exact (Nat.mul_lt_mul_right hP).mp this
  have hcount : q.degree + m = (k + 1) * r := by
    have hmul : (q.degree + m) * P = ((k + 1) * r) * P := by
      rw [add_mul]
      nlinarith [hweight, hR]
    exact Nat.mul_right_cancel hP hmul
  have hselect : r - m ≤ q.degree := by
    have : r ≤ (k + 1) * r := by
      calc r = 1 * r := by simp
        _ ≤ (k + 1) * r := Nat.mul_le_mul_right r (by omega)
    omega
  obtain ⟨c, hc, hdegree⟩ := exists_le_degree_eq q (r - m) hselect
  let g : ι →₀ ℕ := t + equivFunOnFinite.symm (fun i => c i * (P / w i))
  have hgf : g ≤ f := by
    intro i
    change t i + c i * (P / w i) ≤ f i
    rw [← hcoord i]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hc i)) _
  refine ⟨g, hgf, ?_⟩
  rw [hD, show weight w g = weight w t + P * c.degree from ?_, hR, hdegree]
  · have : m + (r - m) = r := Nat.add_sub_of_le (Nat.le_of_lt hm)
    nlinarith
  · change weight w (t + equivFunOnFinite.symm (fun i => c i * (P / w i))) =
      weight w t + P * c.degree
    rw [map_add, weight_eq_sum w (equivFunOnFinite.symm (fun i => c i * (P / w i))),
      degree_eq_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [nsmul_eq_mul, coe_equivFunOnFinite_symm]
    nlinarith [hb i]

/-- Every exponent vector of weight `k * weightedBlockSize w` is a sum of exactly
`k` exponent vectors of weight `weightedBlockSize w`. This includes empty index
types and `k = 0`. -/
theorem exists_weightedBlocks (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (f : ι →₀ ℕ) (hf : weight w f = k * weightedBlockSize w) :
    ∃ g : Fin k → (ι →₀ ℕ), (∑ j, g j) = f ∧
      ∀ j, weight w (g j) = weightedBlockSize w := by
  induction k generalizing f with
  | zero =>
    have hfzero : f = 0 := by
      ext i
      have hle := le_weight w (Nat.ne_of_gt (hw i)) f
      simp only [Nat.zero_mul] at hf
      simpa only [Finsupp.zero_apply] using (by omega : f i = 0)
    refine ⟨Fin.elim0, ?_, ?_⟩
    · simpa using hfzero.symm
    · intro j; exact j.elim0
  | succ k ih =>
    cases isEmpty_or_nonempty ι with
    | inl hempty =>
      have hfzero : f = 0 := by
        ext i
        exact isEmptyElim i
      have hcontra : False := by
        simp [hfzero, weightedBlockSize] at hf
      exact False.elim hcontra
    | inr hnonempty =>
      let : Nonempty ι := hnonempty
      obtain ⟨first, hfirst, hwfirst⟩ :=
        exists_le_weightedBlockSize w hw k f hf
      have hrest : weight w (f - first) = k * weightedBlockSize w := by
        have hsum : first + (f - first) = f := add_tsub_cancel_of_le hfirst
        have := congrArg (weight w) hsum
        simp only [map_add] at this
        rw [hf, hwfirst] at this
        rw [add_mul] at this
        omega
      obtain ⟨rest, hrestsum, hrestweight⟩ := ih (f - first) hrest
      refine ⟨Fin.cons first rest, ?_, ?_⟩
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hrestsum]
        exact add_tsub_cancel_of_le hfirst
      · intro j
        refine Fin.cases ?_ ?_ j
        · exact hwfirst
        · exact hrestweight

end Finsupp
