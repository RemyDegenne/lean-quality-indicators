namespace OAI

noncomputable section

open scoped BigOperators Classical

open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve

open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic

namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O

local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem retained_nonempty_radius {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (A : Source (ι:=ι) J → ℂ) (ψC ψd : ℝ → ℂ)
    (aC bC ad bd Z B θ η : ℝ) (hZ : 1 < Z)
    (hC : Function.support ψC ⊆ Set.Icc aC bC)
    (hd : Function.support ψd ⊆ Set.Icc ad bd)
    (hCup : bC ≤ Z^η) (hdlo : Z^(-η) ≤ ad)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hne : (quotientSet p (retained p S A ψC ψd Z B θ)).Nonempty) :
    1 ≤ Z^((B-θ)+2*η) ∧ 0 ≤ (B-θ)+2*η :=
  nonempty_radius p hp (retained p S A ψC ψd Z B θ) Z (B-θ) η hZ hne
    (retained_quotient_bound p hp S A ψC ψd aC bC ad bd Z B θ η
      (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv)

end SevenEighths.InverseInitialQuotientGeometry
end
end OAI
