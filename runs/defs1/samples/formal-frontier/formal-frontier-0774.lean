@[expose] public section

universe u v w

namespace ProfiniteGrp

namespace IsProcyclic

/-- A procyclic group is modeled by the quotient product for its
generator-independent exponents. The equivalence is noncomputable because
selecting a generator and constructing the quotient model use choice.

This primewise exponent model formalizes the product description in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
(1.7.7); Mathlib supplies the completion and quotient constructions. -/
noncomputable def continuousMulEquivModel
    {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) :
    G ≃ₜ* Multiplicative (primewisePadicQuotientModel.{0} hG.exponents) :=
  primewisePadicContinuousMulEquivModel
    (primewisePadicBaseMapOfGenerator G hG.choose)
    (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)

end IsProcyclic
end ProfiniteGrp
end
