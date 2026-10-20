public section

open WithConv

open scoped TensorProduct

namespace TauCeti.HopfIdeal

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

variable {M : Type w} {N : Type x}

variable [AddCommGroup M] [Module R M] [Comodule R H M]

variable [AddCommGroup N] [Module R N] [Comodule R H N]

variable [Module.Finite R M] [Module.Projective R M]

variable (I : HopfIdeal R H)

attribute [local instance] Comodule.linearHom

section Normal

variable {k : Type u} [Field k] [IsAlgClosed k]

variable [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]

variable {V : Type w} {W : Type x}

variable [AddCommGroup V] [Module k V] [Comodule k H V]

variable [AddCommGroup W] [Module k W] [Comodule k H W]

variable [FiniteDimensional k V] {J : HopfIdeal k H}

@[simp↓]
theorem IsNormal.mem_weightSpaceOneSubcomodule_linearHom_iff (hJ : J.IsNormal) (f : V →ₗ[k] W) :
    f ∈ hJ.weightSpaceOneSubcomodule (V →ₗ[k] W) ↔
      f.baseChange (H ⧸ J.toIdeal) ∘ₗ
          Comodule.endOfPoint V (Ideal.Quotient.mkₐ k J.toIdeal) =
        Comodule.endOfPoint W (Ideal.Quotient.mkₐ k J.toIdeal) ∘ₗ
          f.baseChange (H ⧸ J.toIdeal) := by
  rw [← Subcomodule.mem_toSubmodule, hJ.weightSpaceOneSubcomodule_toSubmodule]
  exact J.mem_weightSpace_linearHom_one_iff f

end Normal
end
end TauCeti.HopfIdeal
end
