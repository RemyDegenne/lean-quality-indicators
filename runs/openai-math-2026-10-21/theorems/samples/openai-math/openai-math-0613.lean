namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial

open NormalBasisRigidity

section KernelCriterion

variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem normalBasis_complement_algebraicIndependent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 → p ∈ Q)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    AlgebraicIndependent C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  classical
  let x : {i // i ∉ A} → E := fun i => φ (X i.val)
  have hφ (p : MvPolynomial {i // i ∉ A} C) : φ (rename Subtype.val p) = aeval x p := by
    have he : φ.comp (rename Subtype.val) = aeval x := by ext i; simp [x]
    exact AlgHom.congr_fun he p
  apply algebraicIndependent_of_pderiv_kernel
  intro p hp j
  obtain ⟨t,ht⟩ := normalBasis_complement_surjective (polynomialTangent φ Q) A hA
    (Pi.single j 1)
  have hmem : rename Subtype.val p ∈ Q := hker _ ((hφ p).trans hp)
  have heq : (∑ i, φ (pderiv i (rename Subtype.val p)) * t.val i) = 0 := by
    exact congrFun t.property ⟨rename Subtype.val p,hmem⟩
  rw [polynomialGradient_rename] at heq
  have hv : ∀ i : {i // i ∉ A}, t.val i.val = (Pi.single j (1 : E) : {i // i ∉ A} → E) i := by
    intro i
    exact congrFun ht i
  simpa [hv, hφ, Pi.single_apply, x] using heq

end KernelCriterion
end PiExponent
end
end OAI
