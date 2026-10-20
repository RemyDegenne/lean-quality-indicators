variable {R L M : Type*} [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L]

namespace LieModule

open Algebra Function LieAlgebra LinearMap Module Module.End Polynomial

open scoped TensorProduct

variable [AddCommGroup M] [LieRingModule L M]

attribute [local instance 100] LieRing.ofAssociativeRing

public theorem isNilpotent_derivedSeries_of_traceForm_eq_zero
    [Module R M] [LieModule R L M] [IsNoetherian R M] [Module.Free R M]
    (h : traceForm R L M = 0) :
    IsNilpotent (derivedSeries R L 1) M := by
  set A := AlgebraicClosure (FractionRing R)
  have _i : FaithfulSMul R A := FaithfulSMul.trans R (FractionRing R) A
  have nilp_ext : IsNilpotent (derivedSeries A (A ⊗[R] L) 1) (A ⊗[R] M) :=
    isNilpotent_derivedSeries_of_traceForm_eq_zero_aux <| by simpa
  rw [isNilpotent_iff_forall' (R := R)]
  rw [isNilpotent_iff_forall' (R := A)] at nilp_ext
  intro ⟨x, hx⟩
  have hx_ext : 1 ⊗ₜ[R] x ∈ derivedSeries A (A ⊗[R] L) 1 := by
    rw [derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  have hbc_inj : Injective (End.baseChangeHom R A M) := LinearMap.baseChangeHom_injective R M A
  have aux : (toEnd R (derivedSeries R L 1) M ⟨x, hx⟩).baseChangeHom R A M =
      (toEnd R L M x).baseChange A := rfl
  rw [← IsNilpotent.map_iff hbc_inj, aux, ← toEnd_baseChange]
  exact nilp_ext ⟨_, hx_ext⟩

end LieModule
