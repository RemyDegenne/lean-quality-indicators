@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} {C : Type v} {I : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C]

namespace Module.Basis

section Maps

variable [CoalgebraStruct R C]

theorem comul_eq_tmul_self_iff_orthogonalIdempotents_repr (b : Module.Basis I R C)
    (hcomul : ∀ i, Coalgebra.comul (R := R) (b i) = b i ⊗ₜ[R] b i)
    (x : C) :
    Coalgebra.comul (R := R) x = x ⊗ₜ[R] x ↔
      OrthogonalIdempotents (fun i ↦ b.repr x i) := by
  classical
  constructor
  · intro hx
    have hcoord (i j : I) :
        b.repr x i * b.repr x j = b.repr x i * b.repr (b i) j := by
      have hij := congrArg (fun t ↦ (b.tensorProduct b).repr t (i, j)) hx
      rw [b.tensorProduct_repr_comul_apply hcomul, tensorProduct_repr_tmul_apply,
        smul_eq_mul] at hij
      simpa only [mul_comm] using hij.symm
    refine ⟨?_, ?_⟩
    · intro i
      change b.repr x i * b.repr x i = b.repr x i
      simpa using hcoord i i
    · intro i j hij
      simpa [b.repr_self_apply, hij] using hcoord i j
  · intro hx
    apply (b.tensorProduct b).repr.injective
    apply Finsupp.ext
    rintro ⟨i, j⟩
    rw [b.tensorProduct_repr_comul_apply hcomul, tensorProduct_repr_tmul_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simpa using (hx.idem i).eq.symm
    · rw [b.repr_self_apply, ite_eq_right hij, mul_zero]
      exact (hx.ortho (Ne.symm hij)).symm

end Maps
end Module.Basis
end
