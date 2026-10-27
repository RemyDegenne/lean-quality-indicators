public noncomputable section

open Function OnePoint Set Topology

open scoped Manifold

universe u v

namespace TauCeti

open RiemannSurface ThricePuncturedSphere

open scoped ContDiff in
/-- An **analytic Belyi pair**: a compact connected Riemann surface `X`, carried by the unbundled
instances on its type, together with a finite holomorphic map `β : X → OnePoint ℂ` to the Riemann
sphere, the **Belyi map**, all of whose branch values lie in `{0, 1, ∞}`.

On a compact connected surface every nonconstant holomorphic map is finite, so `β` is just a
nonconstant holomorphic map (`TauCeti.AnalyticBelyiPair.ofIsCoveringMapOn` builds a pair from
these data). The condition on the branch values says that `β` is a covering map over the
complement of `{0, 1, ∞}` (`TauCeti.AnalyticBelyiPair.isCoveringMapOn`). -/
structure AnalyticBelyiPair : Type (u + 1) where
  /-- The Riemann surface of the pair. -/
  X : Type u
  [instTopologicalSpace : TopologicalSpace X]
  [instChartedSpace : ChartedSpace ℂ X]
  [instIsManifold : IsManifold 𝓘(ℂ) ω X]
  [instT2Space : T2Space X]
  [instCompactSpace : CompactSpace X]
  [instConnectedSpace : ConnectedSpace X]
  /-- The Belyi map of the pair. -/
  β : FiniteHolomorphicMap X (OnePoint ℂ)
  /-- The Belyi map is unramified over every point other than `0`, `1` and `∞`. -/
  branchValues_subset :
    β.branchValues ⊆ {((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), (∞ : OnePoint ℂ)}

end TauCeti
end
