@[expose] public section

open Function MeasureTheory Set

open scoped ComplexConjugate

namespace QuadraticCarleson

namespace KrauseLaceyScalarNear

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction KrauseLaceyOrderedEnergy

attribute [local instance] Classical.propDecidable

theorem norm_signed_badPieceLp_sq_le_mass
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hsmall : ∀ J ∈ N, 1 ≤ scale J)
    (c : RealInterval → ℝ) (hc : ∀ I ∈ N, |c I| ≤ 1) :
    ‖∑ I ∈ N, c I • badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤
      (311040 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∑ I ∈ N, intervalBadMass S f I₀ k₀ s scale I := by
  let C := 103680 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ * (2 : ℝ) ^ (-s)
  have h := norm_sum_sq_le_of_finite_partition N
    (fun I => c I • badPieceLp S f hf I₀ k₀ s scale I)
    (intervalBadMass S f I₀ k₀ s scale) (physicalScaleResidue scale) C (fun r => ?_)
  · convert h using 1
    dsimp [C]
    ring
  · let R (r : Fin 3) := N.filter fun I => physicalScaleResidue scale I = r
    apply norm_signed_badPieceLp_sq_le_of_residue hf I₀ k₀ s hk₀ scale hlam hparent hsub
      (R r) ((Finset.filter_subset _ N).trans hN)
      (fun J hJ ↦ hsmall J (Finset.mem_filter.mp hJ).1) _ c
      (fun I hI ↦ hc I (Finset.mem_filter.mp hI).1)
    intro I hI J hJ
    exact physicalScaleResidue_eq_imp_mod_eq scale
      ((Finset.mem_filter.mp hI).2.trans (Finset.mem_filter.mp hJ).2.symm)

end KrauseLaceyScalarNear
end QuadraticCarleson
end
