namespace P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt

set_option autoImplicit false

namespace P2mUnrFlat

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

scoped instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

p2m_reactivate

p2m_reactivate

scoped instance (N : Type) [AddCommGroup N] : AddCommGroup (Triv N) := inferInstanceAs (AddCommGroup N)

scoped instance (N : Type) [Finite N] : Finite (Triv N) := inferInstanceAs (Finite N)

scoped instance trivDistribMulAction (N : Type) [AddCommGroup N] : DistribMulAction Γℚ (Triv N) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

def TwFun (S N : Type) : Type := S → N

end P2mUnrFlat
end P2MW.S_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isUnramifiedAt
