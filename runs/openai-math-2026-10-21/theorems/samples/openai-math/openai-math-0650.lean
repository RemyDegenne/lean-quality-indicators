namespace OAI

noncomputable section

open scoped BigOperators

namespace PD4Tensor.Spreading

variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι]

theorem algebraic_family_finiteType (n : ι → ℕ)
    (f : ∀ i,MvPowerSeries (Fin (n i)) K)
    (hf : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (f i)) (extra : Finset K) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A ∧
      (∀ x∈extra,x∈A) ∧ ∀ i d,MvPowerSeries.coeff d (f i)∈A := by
  classical
  choose B hB hcoef using fun i => algebraic_series_finiteType (f i) (hf i)
  have hfg : ∀ i,(B i).FG := fun i => (Subalgebra.fg_iff_finiteType (B i)).mpr (hB i)
  choose gens hgens using hfg
  let s := Finset.univ.biUnion gens ∪ extra
  let A := Algebra.adjoin ℤ (s : Set K)
  have hBA : ∀ i,B i≤A := by
    intro i
    rw [←hgens i]
    apply Algebra.adjoin_mono
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩)
  refine ⟨A,Algebra.FiniteType.adjoin_of_finite s.finite_toSet,?_,?_⟩
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · intro i d
    exact hBA i (hcoef i d)

end PD4Tensor.Spreading
end
end OAI
