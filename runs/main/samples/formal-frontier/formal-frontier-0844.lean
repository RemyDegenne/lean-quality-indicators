@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {C : Type v} {I : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C]

namespace Module.Basis

section GroupLike

variable [Coalgebra R C]

theorem isGroupLikeElem_iff_pairwise_mul_eq_zero_and_sum_eq_one
    (b : Module.Basis I R C) (hb : ∀ i, IsGroupLikeElem R (b i)) (x : C) :
    IsGroupLikeElem R x ↔
      Pairwise (fun i j ↦ b.repr x i * b.repr x j = 0) ∧
        (b.repr x).sum (fun _ r ↦ r) = 1 := by
  have hcounit := b.counit_eq_sum_repr (fun i ↦ (hb i).counit_eq_one) x
  have hcomul := b.comul_eq_tmul_self_iff_orthogonalIdempotents_repr
    (fun i ↦ (hb i).comul_eq_tmul_self) x
  constructor
  · intro hx
    exact ⟨(hcomul.mp hx.comul_eq_tmul_self).ortho, hcounit.symm.trans hx.counit_eq_one⟩
  · rintro ⟨hortho, hsum⟩
    refine ⟨hcounit.trans hsum, hcomul.mpr ?_⟩
    classical
    have hcomplete : CompleteOrthogonalIdempotents
        (fun i : (b.repr x).support ↦ b.repr x i) := by
      apply CompleteOrthogonalIdempotents.iff_ortho_complete.mpr
      refine ⟨?_, ?_⟩
      · intro i j hij
        exact hortho (fun h ↦ hij (Subtype.ext h))
      · simpa only [Finset.sum_coe_sort, Finsupp.sum] using hsum
    refine ⟨?_, hortho⟩
    intro i
    by_cases hi : i ∈ (b.repr x).support
    · exact hcomplete.idem ⟨i, hi⟩
    · have hzero : b.repr x i = 0 := Finsupp.notMem_support_iff.mp hi
      simp only [hzero, isIdempotentElem_iff, zero_mul]

end GroupLike
end Module.Basis
end
