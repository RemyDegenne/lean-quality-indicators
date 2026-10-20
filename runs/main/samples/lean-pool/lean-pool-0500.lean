@[expose] public section

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace SphereOddDegree

theorem isZero_singularHomologyℤ_of_contractibleSpace (k : ℕ) (hk : 1 ≤ k)
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero ((singularHomologyℤ k).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  apply IsZero.of_iso _ (singularHomologyℤIsoOfHomotopyEquivSpace k e)
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{0} ℤ) k (ModuleCat.of ℤ ℤ) (TopCat.of Unit) (by omega)

end SphereOddDegree
end
end
