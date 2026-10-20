namespace P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing

set_option autoImplicit false

theorem solution
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K]
    (H : Type*) [CommRing H] [Algebra A H] [Module.Finite A H] [Module.Flat A H]
    (ψ : H →ₐ[A] IsLocalRing.ResidueField A) :
    ∃ φ : H →ₐ[A] A, ∀ h : H, IsLocalRing.residue A (φ h) = ψ h := by

  have hint : (algebraMap A H).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have hnzd : ∀ b : A, b ≠ 0 → algebraMap A H b ∈ nonZeroDivisors H := by
    intro b hb
    have hreg : IsSMulRegular H b :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb)
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
    apply hreg
    show b • x = b • (0 : H)
    rw [smul_zero, Algebra.smul_def, mul_comm]
    exact hx

  haveI : (RingHom.ker ψ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨lam, h1, h2⟩ :=
    GenLift.exists_ringHom_forall_sub_mem A K (algebraMap A H) hint hnzd (RingHom.ker ψ.toRingHom)

  refine ⟨{ lam with commutes' := h1 }, fun h => ?_⟩

  have hk : h - algebraMap A H (lam h) ∈ RingHom.ker ψ.toRingHom := h2 h
  rw [RingHom.mem_ker] at hk
  change ψ (h - algebraMap A H (lam h)) = 0 at hk
  rw [map_sub, sub_eq_zero, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq] at hk
  exact hk.symm

end P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing
