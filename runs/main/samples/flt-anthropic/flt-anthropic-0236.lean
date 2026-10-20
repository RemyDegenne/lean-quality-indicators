namespace P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential

set_option autoImplicit false

open Topology TensorProduct

namespace EtaleCoordK1a

variable {S : Type} [CommRing S]

theorem rankAtStalk_eq [IsDomain S] {M : Type} [AddCommGroup M] [Module S M] [Module.FinitePresentation S M]
    [Module.Flat S M] {n : ℕ} (hrank : Module.rank S M = n) (p : PrimeSpectrum S) : Module.rankAtStalk M p = n := by
  rw [(Module.isLocallyConstant_rankAtStalk (R := S) (M := M)).apply_eq_of_preconnectedSpace p ⟨⊥, Ideal.isPrime_bot⟩]
  have hle : (⊥ : Ideal S).primeCompl ≤ nonZeroDivisors S := by
    intro x hx
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hx (h0 ▸ (Submodule.zero_mem ⊥ : (0 : S) ∈ (⊥ : Ideal S))))
  have hr : Module.rank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = n := by
    rw [IsLocalization.rank_eq (S := Localization.AtPrime (⊥ : Ideal S)) (p := (⊥ : Ideal S).primeCompl) (hp := hle),
      IsLocalizedModule.rank_eq (p := (⊥ : Ideal S).primeCompl) (f := LocalizedModule.mkLinearMap (⊥ : Ideal S).primeCompl M)
        (hp := hle), hrank]
  show Module.finrank (Localization.AtPrime (⊥ : Ideal S)) (LocalizedModule (⊥ : Ideal S).primeCompl M) = n
  exact Module.finrank_eq_of_rank_eq (by rw [hr])

end EtaleCoordK1a
end P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential
