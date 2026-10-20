public section

open scoped TensorProduct

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

theorem geometricallyConnectedCommHopfAlgProperty.of_baseChange
    (k : Type u) (K : Type w) [Field k] [Field K] [Algebra k K]
    (H : CommHopfAlgCat.{v} k)
    (hH : geometricallyConnectedCommHopfAlgProperty K
      (CommHopfAlgCat.baseChange (K := K) H)) :
    geometricallyConnectedCommHopfAlgProperty k H := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro L _ _
  let d := Algebra.TensorProduct.commonOverfield k K L
  have hΩ : ConnectedSpace (PrimeSpectrum ((H : Type v) ⊗[k] d.Ω)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv (d.comparison H)).connectedSpace_iff.mp
      (hH.connectedSpace_tensorProduct K d.Ω (CommHopfAlgCat.baseChange (K := K) H))
  exact connectedSpace_primeSpectrum_of_injective (d.map H).toRingHom (d.map_injective H)

end TauCeti
end
