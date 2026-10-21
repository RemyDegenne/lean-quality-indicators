namespace OAI

noncomputable section

namespace PiExponentJets.W24

open PiExponentSiegel.W23 PiExponentSiegelAux.W09

open PiExponentJets.PolynomialLocalResidueResolution

variable (k σ : Type*) [Field k] [Finite σ]

variable (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime] [Q.IsPrime]

theorem polynomial_prime_pair_local_dimension (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  classical
  let := Fintype.ofFinite σ
  let e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ)
  let P' := P.map e.toRingHom
  let Q' := Q.map e.toRingHom
  have : P'.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e
  have hd := fin_polynomial_prime_pair_local_dimension k (Fintype.card σ) P' Q'
    (Ideal.map_mono hPQ)
  have hl := (ringEquiv_localQuotient e.toRingEquiv P Q).ringKrullDim
  have hp := (Ideal.quotientEquiv P P' e.toRingEquiv rfl).ringKrullDim
  have hq := (Ideal.quotientEquiv Q Q' e.toRingEquiv rfl).ringKrullDim
  rw [← hl, ← hp, ← hq] at hd
  exact hd

end PiExponentJets.W24
end
end OAI
