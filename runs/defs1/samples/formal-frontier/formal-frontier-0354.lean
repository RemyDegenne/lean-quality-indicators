@[expose] public section

namespace MvPolynomial

variable {ι S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (w : ι → ℕ) (x : ∀ i : ι, 𝒮 (w i))

/-- Ordinary polynomial evaluation, bundled as a degree-preserving ring map. -/
noncomputable def weightedAevalGradedHom :
    (weightedHomogeneousSubmodule (𝒮 0) w) →+*ᵍ 𝒮 := by
  let _ : GradedAlgebra (weightedHomogeneousSubmodule (𝒮 0) w) :=
    weightedGradedAlgebra (𝒮 0) w
  exact { (aeval (fun i => (x i : S))).toRingHom with
    map_mem := fun hp => hp.aeval_mem 𝒮 w x }

end MvPolynomial
end
