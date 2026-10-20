@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

namespace IsProcyclic

/-- A procyclic profinite group is continuously equivalent to the support
product of its generator-independent primewise exponents. The equivalence
uses a chosen generator; it requires no torsion-freeness assumption.

The finite-cyclic and p-adic product description comes from Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. I §7, before Proposition (1.7.7); this model explicitly
omits zero exponents. -/
noncomputable def continuousMulEquivSupportProduct
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) :
    G ≃ₜ* Multiplicative (primewisePadicSupportProduct.{0} hG.exponents) :=
  hG.continuousMulEquivModel.trans
    (primewisePadicQuotientModelContinuousMulEquivSupportProduct hG.exponents)

end IsProcyclic
end ProfiniteGrp
end
