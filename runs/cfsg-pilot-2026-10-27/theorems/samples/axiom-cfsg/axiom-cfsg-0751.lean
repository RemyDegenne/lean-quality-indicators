public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

open ReeTag

section Conj

variable {m : ℕ} {K : Type} [Field K] [CharP K F4.prime]

theorem weylOne_conj_sylowX
    {r r' : ℕ} (h : (r, r') ∈ weylOnePairs) (c : K) :
    weylOne K * sylowX K r c * (weylOne K)⁻¹ = sylowX K r' c := by
  obtain ⟨⟨h1, h2⟩, hw⟩ := weylOnePairs_check _ h
  rw [sylowX, sylowX, canonicalRep_mul_pinnedX_mul_inv_of_two F4_two_eq_zero _
    (sylowRoot_pos h1 h2).1, fixedOrbitElement_smul]
  exact congrArg (fun α => pinnedX F4.tag K α c) hw

end Conj
end CFSG.LieType.Ree.LargeReeInvolution
end
