public section

open Finset

namespace AddMonoid.End

variable {A : Type*} [AddCommGroup A] (sigma : AddMonoid.End A) (m : ℕ)

theorem cyclicNorm_ker_eq_one_sub_range (_hpositive : 0 < m) (hperiod : sigma ^ m = 1)
    (hinjective : Function.Injective (nsmulAddMonoidHom (α := A) m))
    (hlift : ∀ a : A, sigma a - a ∈ (nsmulAddMonoidHom (α := A) m).range →
      ∃ z : A, sigma z = z ∧ a - z ∈ (nsmulAddMonoidHom (α := A) m).range) :
    (∑ i ∈ Finset.range m, sigma ^ i).ker = (1 - sigma).range := by
  let difference : AddMonoid.End A := 1 - sigma
  let norm : AddMonoid.End A := ∑ i ∈ Finset.range m, sigma ^ i
  have hnorm_mul : norm * difference = 0 := by
    dsimp [norm, difference]
    rw [geom_sum_mul_neg, hperiod, sub_self]
  change norm.ker = difference.range
  ext v
  constructor
  · intro hv
    let partialSum : AddMonoid.End A := ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range i, sigma ^ j
    have hpartial : difference * partialSum = m • (1 : AddMonoid.End A) - norm := by
      dsimp [partialSum, difference, norm]
      rw [Finset.mul_sum]
      simp_rw [mul_neg_geom_sum]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
    let w : A := partialSum v
    have hw : difference w = m • v := by
      have heq := congrArg (fun f : AddMonoid.End A => f v) hpartial
      change difference (partialSum v) = m • v - norm v at heq
      have hvzero : norm v = 0 := hv
      simpa only [w, hvzero, sub_zero] using heq
    have hwmem : sigma w - w ∈ (nsmulAddMonoidHom (α := A) m).range := by
      refine ⟨-v, ?_⟩
      change m • (-v) = sigma w - w
      have : difference w = w - sigma w := by rfl
      rw [this] at hw
      simpa only [neg_nsmul, neg_sub] using (congrArg Neg.neg hw).symm
    obtain ⟨z, hzfixed, ⟨b, hb⟩⟩ := hlift w hwmem
    have hdz : difference z = 0 := by
      change z - sigma z = 0
      rw [hzfixed, sub_self]
    have heq : m • v = m • difference b := by
      calc
        m • v = difference w := hw.symm
        _ = difference (w - z) := by simp [map_sub, hdz]
        _ = difference (m • b) := by rw [← hb]; rfl
        _ = m • difference b := map_nsmul difference m b
    refine ⟨b, ?_⟩
    exact hinjective heq.symm
  · rintro ⟨b, rfl⟩
    change norm (difference b) = 0
    have heq := congrArg (fun f : AddMonoid.End A => f b) hnorm_mul
    exact heq

end AddMonoid.End
end
