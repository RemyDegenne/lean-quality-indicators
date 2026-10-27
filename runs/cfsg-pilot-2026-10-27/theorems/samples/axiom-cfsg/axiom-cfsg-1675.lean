open CFSG

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v

universe u

public theorem section13_typeP_prTIres_pf4_primeTIirr_spec_base_principal_source
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (ω : ℕ → ℕ → Section1.ClassFunction W)
    (η : ℕ → ℕ → Section1.ClassFunction G)
    (μ : ℕ → ℕ → Section1.ClassFunction Smax)
    (ν : ℕ → ℕ → Section1.ClassFunction Tmax)
    (μsum : ℕ → Section1.ClassFunction Smax)
    (νsum : ℕ → Section1.ClassFunction Tmax)
    (δ δ' : ℕ → ℤ)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (_hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (_hnotation : hypothesis_13_1_characterNotationDataFor Smax Tmax W W1 W2 p q
      ω η μ ν μsum νsum δ δ' σ) :
    μ 0 0 = Section1.principalCharacter Smax := by
  rcases
      section13_typeP_prTIres_pf4_primeTIirr_spec_cyclicTI_base_source
        Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
        ω η μ ν μsum νsum δ δ' σ p q u v c d _hsource _hnotation with
    ⟨hsignedBase, hδ0⟩
  simpa [hδ0] using hsignedBase

end CFSG.Section13
end
