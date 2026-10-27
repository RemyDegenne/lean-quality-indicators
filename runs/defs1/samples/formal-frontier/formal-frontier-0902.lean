set_option autoImplicit false

set_option relaxedAutoImplicit false

@[expose] public section

open scoped TensorProduct

universe uR uM

namespace TrivSqZeroExt

variable {R : Type uR} {M : Type uM}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

scoped instance canonicalOppositeModule : Module Rᵐᵒᵖ M :=
  Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom

scoped instance canonicalCentralScalar : IsCentralScalar R M where
  op_smul_eq_smul _ _ := rfl

section ProjectionBaseChange

local instance : Algebra (TrivSqZeroExt R M) R := algebraBase R M

/-- Projection-base change of the square-zero kernel, as an `R`-linear equivalence. -/
noncomputable def kerIdealBaseChange :
    R ⊗[TrivSqZeroExt R M] kerIdeal R M ≃ₗ[R] M := by
  letI : Module (TrivSqZeroExt R M) M :=
    Module.compHom M (algebraMap (TrivSqZeroExt R M) R)
  letI : IsScalarTower (TrivSqZeroExt R M) R M := by
    constructor
    intro s r m
    change (s.fst * r) • m = s.fst • (r • m)
    rw [mul_smul]
  letI : TensorProduct.CompatibleSMul (TrivSqZeroExt R M) R R M :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective R M
      (fun r : R => ⟨inl r, rfl⟩)
  let equivalence : kerIdeal R M ≃ₗ[TrivSqZeroExt R M] M :=
    { (kerIdealLinearEquiv (R := R) (M := M)).toAddEquiv with
      map_smul' := by
        intro s j
        change (s * j.val).snd = s.fst • j.val.snd
        rw [(mem_kerIdeal_iff_inr R M j.val).1 j.property]
        change (s * inr j.val.snd).snd = s.fst • j.val.snd
        conv_lhs => rw [← inl_fst_add_inr_snd_eq s]
        simp [add_mul, inl_mul_inr] }
  exact equivalence.baseChange (TrivSqZeroExt R M) R (kerIdeal R M) M ≪≫ₗ
    TensorProduct.lidOfCompatibleSMul (TrivSqZeroExt R M) R M

end ProjectionBaseChange
end TrivSqZeroExt
end
