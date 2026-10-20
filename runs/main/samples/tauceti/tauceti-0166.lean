public section

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X]

lemma MulAction.orbitRelQuotient_smul_eq_base_iff [IsCancelSMul G X] (H : Subgroup G) (g : G)
    (x : X) :
    (Quotient.mk'' (g • x) : MulAction.orbitRel.Quotient H X) =
        Quotient.mk'' x ↔
      g ∈ H := by
  simpa using MulAction.orbitRelQuotient_smul_eq_smul_iff_mul_inv_mem H x g 1

end TauCeti
end
