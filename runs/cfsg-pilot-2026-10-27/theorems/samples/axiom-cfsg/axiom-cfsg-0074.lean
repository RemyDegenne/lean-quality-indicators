public noncomputable section

open Matrix QuadraticMap

open scoped commutatorElement

open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive

open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow

open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel

open CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK.Proofs2.Sp48

open CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane

open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

open CFSG.ComponentClassification.CatalogueBOrthogonal

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem P_map_conj_s (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hP : P = wreathO F W.D ⊓ G) :
    P.map (swapConjHom F) = P := by
  letI : G.Normal := Subgroup.Normal.of_commutator_le
    (G := TauCeti.QuadraticMap.orthogonalGroup Q) hLG
  have hG : Subgroup.map (swapConjHom F) G = G := by
    simpa using Subgroup.Normal.map_conj_eq G F.sO
  have hTw : Subgroup.map (swapConjHom F) (wreathO F W.D) = wreathO F W.D := by
    have hs : F.sO ∈ wreathO F W.D :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    simpa [swapConjHom] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs))
  rw [hP, Subgroup.map_inf _ _ (swapConjHom F) (swapConjHom_injective F), hTw, hG]

end CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow
end
