@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

namespace groupCohomology

section Differentials

open ShortComplex

/-- The short complex `Fun(G, A) --d₁₂--> Fun(G × G, A) --d₂₃--> Fun(G × G × G, A)`. -/
@[simps! -isSimp f g]
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  mk (d₁₂ A) (d₂₃ A) (d₁₂_comp_d₂₃ A)

end Differentials
end groupCohomology
end
end
