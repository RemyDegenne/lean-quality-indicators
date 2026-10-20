@[expose] public section

open Module nonZeroDivisors

variable (A K L L₂ L₃ B B₂ B₃ : Type*)

variable [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]

variable [Algebra A B] [Algebra A B₂] [Algebra A B₃]

variable [Field K] [Field L] [Field L₂] [Field L₃]

variable [Algebra A K] [IsFractionRing A K]

variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]

variable [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]

variable [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

variable [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]

variable [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]

variable [FiniteDimensional K L]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {Aₘ Bₘ} [CommRing Aₘ] [CommRing Bₘ] [Algebra Aₘ Bₘ] [Algebra A Aₘ] [Algebra B Bₘ]

variable [Algebra A Bₘ] [IsScalarTower A Aₘ Bₘ] [IsScalarTower A B Bₘ]

variable (M : Submonoid A) [IsLocalization M Aₘ]

variable [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₘ]

section trace

variable {A K L B}

variable (A B)

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B]

variable [Module.Finite A B] [IsTorsionFree A B]

variable {A B}

lemma Algebra.algebraMap_intTrace (x : B) :
    algebraMap A K (Algebra.intTrace A B x) = Algebra.trace K L (algebraMap B L x) := by
  have : IsIntegralClosure B A (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  apply (FractionRing.algEquiv A K).symm.injective
  rw [AlgEquiv.commutes, Algebra.intTrace, Algebra.map_intTraceAux,
    ← AlgEquiv.commutes (FractionRing.algEquiv B L)]
  apply Algebra.trace_eq_of_equiv_equiv (FractionRing.algEquiv A K).toRingEquiv
    (FractionRing.algEquiv B L).toRingEquiv
  ext
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K) (FractionRing.algEquiv B L) _

end trace
end
