@[expose] public section

namespace MvPolynomial

variable {ι S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (w : ι → ℕ) (x : ∀ i : ι, 𝒮 (w i))

theorem aeval_weightedHomogeneousComponent (n : ℕ) (p : MvPolynomial ι (𝒮 0)) :
    aeval (fun i => (x i : S)) (weightedHomogeneousComponent w n p) =
      (DirectSum.decompose 𝒮 (aeval (fun i => (x i : S)) p) n : S) := by
  classical
  let _ : GradedAlgebra (weightedHomogeneousSubmodule (𝒮 0) w) :=
    weightedGradedAlgebra (𝒮 0) w
  have h := (weightedAevalGradedHom 𝒮 w x).map_directSumDecompose
    (x := p) (i := n)
  have hcomponent : (DirectSum.decompose (weightedHomogeneousSubmodule (𝒮 0) w) p n :
      MvPolynomial ι (𝒮 0)) = weightedHomogeneousComponent w n p := by
    exact weightedDecomposition.decompose'_apply (𝒮 0) w p n
  rw [hcomponent] at h
  exact h

end MvPolynomial
end
