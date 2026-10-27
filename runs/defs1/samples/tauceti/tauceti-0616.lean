public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

namespace ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw) {k l : ℕ}

/-- A law is **dissociated** when restrictions to disjoint label windows are independent: the
level-`(k + l)` marginal pushed to the pair of windows is the product of the level-`k` and
level-`l` marginals. -/
def IsDissociated : Prop :=
  ∀ k l : ℕ,
    (L.law (k + l)).map
        (fun G => (SimpleGraph.comap (Fin.castAdd l) G, SimpleGraph.comap (Fin.natAdd k) G))
      = (L.law k).prod (L.law l)

end ExchangeableGraphLaw
end DenseGraphLimits
end TauCeti
end
end
