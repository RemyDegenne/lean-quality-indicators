public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace OrderSystem

variable {X G : Type*} [AddCommGroup G] (S : OrderSystem X G)

noncomputable section

lemma principalHom_injective_of_principalKernel_eq_bot (h : S.principalKernel = ⊥) :
    Function.Injective S.principalHom :=
  S.principalKernel_eq_bot_iff.mp h

end
end OrderSystem
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
