public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti

universe u

namespace TopPair

variable (k : Type u) [Ring k]

theorem singularRelπ_hom_ext {P : TopPair.{u}} {T : ChainComplex (ModuleCat.{u} k) ℕ}
    {g g' : P.singularChainComplex (ModuleCat.of k k) ⟶ T}
    (h : singularRelπ k P ≫ g = singularRelπ k P ≫ g') : g = g' :=
  Cofork.IsColimit.hom_ext (P.isColimitCokernelCoforkSingularChainComplex _) h

end TopPair
end
end
