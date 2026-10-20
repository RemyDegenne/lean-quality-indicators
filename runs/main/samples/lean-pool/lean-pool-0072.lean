@[expose] public section

namespace EGZ.FlagDecomposition.CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

theorem refined_level_le (x : (D.split hp hδ hsmall).flag.Node) :
    Φ.level x.1.1.1.1 ≤ (D.refined hp hδ hsmall C hmod hcenter).level x := by
  apply Φ.representation.level_le_of_space_le_of_factor
    (D.refined hp hδ hsmall C hmod hcenter).representation x.1.1.1.1 x
    ((Augmented.forget (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
      (D.extra_antitone hp hδ hsmall) C x).modp p)
    (D.refined_space_le_original hp hδ hsmall C hmod hcenter x)
  intro v hv
  exact (D.refined_forget_map hp hδ hsmall C hmod hcenter x v hv).symm

end EGZ.FlagDecomposition.CompletePreparation
end
