public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Steinberg.Adjoint Polynomial

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section PolyFrob

variable {L : Type} [Field L] {V : Type*} [AddCommGroup V] [Module L V]

theorem commute_of_frob_pair {ι : Type*} (F G : ℕ → Module.End L (ι →₀ L))
    {q : ℕ} (hq : 3 ≤ q) (z : Module.End L (ι →₀ L)) (T : Finset L)
    (hT : 2 + q * 2 < T.card)
    (hz : ∀ c ∈ T, z * ((∑ i ∈ Finset.range 3, c ^ i • F i) *
        (∑ j ∈ Finset.range 3, (c ^ q) ^ j • G j)) =
      ((∑ i ∈ Finset.range 3, c ^ i • F i) * (∑ j ∈ Finset.range 3, (c ^ q) ^ j • G j)) * z)
    {i₀ j₀ : ℕ} (hi₀ : i₀ < 3) (hj₀ : j₀ < 3) :
    z * (F i₀ * G j₀) = (F i₀ * G j₀) * z := by
  classical
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  set A : ℕ → ℕ → L := fun i j => (z * (F i * G j)) (Finsupp.single b 1) a with hA
  set B : ℕ → ℕ → L := fun i j => ((F i * G j) * z) (Finsupp.single b 1) a with hB
  set P : L[X] := ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
    C (A i j - B i j) * X ^ (i + q * j) with hP
  have hzero : ∀ c ∈ T, P.eval c = 0 := by
    intro c hc
    have h1 := congrArg (fun M : Module.End L (ι →₀ L) => M (Finsupp.single b 1) a) (hz c hc)
    rw [mul_sum_entry, sum_mul_entry] at h1
    rw [hP, eval_finsetSum]
    have h2 : ∀ i j, (C (A i j - B i j) * X ^ (i + q * j)).eval c =
        (c ^ i * (c ^ q) ^ j) * A i j - (c ^ i * (c ^ q) ^ j) * B i j := by
      intro i j
      rw [eval_mul, eval_C, eval_pow, eval_X, pow_add, pow_mul]
      ring
    simp only [eval_finsetSum, h2, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact h1
  have hdeg : P.natDegree ≤ 2 + q * 2 := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have hi' : i ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hj' : j ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have := Nat.mul_le_mul_left q hj'
    omega
  have hP0 : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P T hzero
    (lt_of_le_of_lt hdeg hT)
  have hcoeff := congrArg (fun P : L[X] => P.coeff (i₀ + q * j₀)) hP0
  simp only [coeff_zero] at hcoeff
  rw [hP, finsetSum_coeff, Finset.sum_eq_single i₀] at hcoeff
  · rw [finsetSum_coeff, Finset.sum_eq_single j₀] at hcoeff
    · rw [coeff_C_mul_X_pow, ite_eq_left rfl, sub_eq_zero] at hcoeff
      exact hcoeff
    · intro j _ hj
      rw [coeff_C_mul_X_pow, ite_eq_right]
      intro h
      exact hj (eq_of_add_mul_eq (by omega) (by omega) h).2.symm
    · intro h
      exact absurd (Finset.mem_range.2 hj₀) h
  · intro i hi hi'
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul_X_pow, ite_eq_right]
    intro h
    exact hi' (eq_of_add_mul_eq (by omega) (by have := Finset.mem_range.1 hi; omega) h).1.symm
  · intro h
    exact absurd (Finset.mem_range.2 hi₀) h

end PolyFrob
end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
