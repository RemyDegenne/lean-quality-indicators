@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

namespace IsProcyclic

/-- A torsion-free procyclic profinite group is continuously equivalent to
the product of p-adic integers indexed by its infinite-exponent primes.
The support is generator-independent, but the equivalence uses a chosen
topological generator.

The torsion-free p-adic product is described in Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §7, before Proposition (1.7.7). -/
noncomputable def continuousMulEquivTopSupport
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) :
    G ≃ₜ* Multiplicative
      (∀ p : {p : Nat.Primes // hG.exponents p = ⊤}, ULift.{0} ℤ_[p.1]) :=
  hG.continuousMulEquivModel.trans
    (primewisePadicQuotientModelContinuousMulEquivTopSupport hG.exponents
      ((primewisePadicSurjective_isMulTorsionFree_iff
        (primewisePadicBaseMapOfGenerator G hG.choose)
        (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)).mp
          hfree))

end IsProcyclic
end ProfiniteGrp
end
