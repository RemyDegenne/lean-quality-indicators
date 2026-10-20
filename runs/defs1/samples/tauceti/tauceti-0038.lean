public noncomputable section

open Function OnePoint Set Topology

open scoped Manifold

universe u v

namespace TauCeti

open RiemannSurface ThricePuncturedSphere

attribute [instance] AnalyticBelyiPair.instTopologicalSpace AnalyticBelyiPair.instChartedSpace
  AnalyticBelyiPair.instIsManifold AnalyticBelyiPair.instT2Space
  AnalyticBelyiPair.instCompactSpace AnalyticBelyiPair.instConnectedSpace

namespace AnalyticBelyiPair

/-- **The permutation triple of an isomorphism class of analytic Belyi pairs** of degree `n`: the
isomorphism class of the monodromy triple of any representative, for any numbering of its fibre
over `1/2` (`TauCeti.AnalyticBelyiPair.toIsoClass_mk`). It is well defined because isomorphic
pairs have isomorphic monodromy triples
(`TauCeti.AnalyticBelyiPair.Iso.isoClass_monodromyTriple_eq`). -/
def toIsoClass (n : ℕ) : Quotient (isoSetoid.{u} n) → PermutationTriple.IsoClass n :=
  Quotient.lift
    (fun P ↦ .mk (P.1.isCoveringMap_restrict.monodromyTriple
      ((P.1.nonempty_restrict_preimage_singleton_equiv basePt).some.trans (finCongr P.2))))
    fun _ _ ⟨e⟩ ↦ (e.isoClass_monodromyTriple_eq _ _).symm

end AnalyticBelyiPair
end TauCeti
end
