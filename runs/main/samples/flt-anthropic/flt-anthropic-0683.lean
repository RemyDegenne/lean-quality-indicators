namespace P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open scoped TensorProduct

open WithConv

p2m_reactivate

p2m_reactivate

theorem FREEK_hinj {Rh : Type} [CommRing Rh] [IsLocalRing Rh] {p : ℕ} [Fact p.Prime] [Algebra Rh (ZMod p)]
    (hker : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal Rh)
    {A B : Type} [CommRing A] [Algebra Rh A] [CommRing B] [Algebra Rh B] (f : B →ₗ[Rh] A)
    (hinj : Function.Injective (f.lTensor (ZMod p))) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField Rh)) := by
  classical
  have hsurj : Function.Surjective (Algebra.ofId Rh (ZMod p)) := ZMod.ringHom_surjective (algebraMap Rh (ZMod p))
  have hkereq : IsLocalRing.maximalIdeal Rh = RingHom.ker (Algebra.ofId Rh (ZMod p) : Rh →+* ZMod p) := by
    ext x; rw [RingHom.mem_ker]; exact (hker x).symm
  let e : IsLocalRing.ResidueField Rh ≃ₐ[Rh] ZMod p :=
    (Ideal.quotientEquivAlgOfEq Rh hkereq).trans (Ideal.quotientKerAlgEquivOfSurjective hsurj)
  let eB := (e.toLinearEquiv.rTensor B : IsLocalRing.ResidueField Rh ⊗[Rh] B ≃ₗ[Rh] ZMod p ⊗[Rh] B)
  let eA := (e.toLinearEquiv.rTensor A : IsLocalRing.ResidueField Rh ⊗[Rh] A ≃ₗ[Rh] ZMod p ⊗[Rh] A)
  have hcomm : ∀ x, eA ((f.lTensor (IsLocalRing.ResidueField Rh)) x) = (f.lTensor (ZMod p)) (eB x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  have := congrArg eA hxy
  rw [hcomm, hcomm] at this
  exact eB.injective (hinj this)

end P2MW.S_ModularCurve_exists_hopfCokernel_free_finrank_eq_pow_of_finPtsWitness
