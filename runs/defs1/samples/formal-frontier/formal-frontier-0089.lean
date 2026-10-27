@[expose] public section

set_option warningAsError true

namespace MvPolynomial

variable {S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Evaluation by all degree-one elements as a degree-preserving graded map. -/
noncomputable def aevalDegreeOneGradedHom :
    (homogeneousSubmodule (𝒮 1) (𝒮 0)) →+*ᵍ 𝒮 := by
  letI : GradedAlgebra (homogeneousSubmodule (𝒮 1) (𝒮 0)) := gradedAlgebra
  exact { (aeval (fun a : 𝒮 1 => (a : S))).toRingHom with
    map_mem := fun hp => isHomogeneous_aeval_degreeOne 𝒮 hp }

end MvPolynomial
end
