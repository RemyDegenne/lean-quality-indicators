namespace OAI

section

section

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace CubicTorus

theorem isMinimizerAt_axis_strict_normal_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (i : Fin 3)
    (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) :
    (∀ x∈frontier (openRepresentative E),N (representative x) i=0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      N (representative x) i<0) ∨
    (∀ x∈frontier (openRepresentative E),Real.sin (2*Real.pi*representative x i)<0 →
      0<N (representative x) i) := by
  let e := coordinatePermutation (Equiv.swap 0 i)
  let F := e.torus ⁻¹' E
  have hF : MeasurableSet F := hE.preimage e.torus.continuous.measurable
  have hmF : IsMinimizerAt V F := e.isMinimizerAt hmin
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by
    change IsPreconnected (frontier (openRepresentative (e.torus ⁻¹' E)))
    rw [e.frontier_openRepresentative_preimage hE]
    exact e.torus.toHomeomorph.isPreconnected_preimage.mpr hc
  have hRF : F=ᵐ[torusVolume](torusFirstReflection ⁻¹' F) := by
    have hh := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq hR
    filter_upwards [hh] with x hx
    change (e.torus x∈E)=((axisReflection i).torus (e.torus x)∈E) at hx
    change (e.torus x∈E)=(e.torus (torusFirstReflection x)∈E)
    change (torusCoordinatePermute (Equiv.swap 0 i) x∈E)=
      ((axisReflection i).torus (torusCoordinatePermute (Equiv.swap 0 i) x)∈E) at hx
    rwa [axisReflection_conjugate] at hx
  have hpoint (x : Torus) (hx : x∈frontier (openRepresentative E)) :
      e.torus x∈frontier (openRepresentative F) := by
    change e.torus x∈frontier (openRepresentative (e.torus ⁻¹' E))
    rw [e.frontier_openRepresentative_preimage hE]
    change e.torus (e.torus x)∈frontier (openRepresentative E)
    change torusCoordinatePermute (Equiv.swap 0 i)
      (torusCoordinatePermute (Equiv.swap 0 i) x)∈frontier (openRepresentative E)
    rwa [torusCoordinateSwap_involutive]
  have hseam (x : Torus) : firstSeamFunction (representative (e.torus x))=
      Real.sin (2*Real.pi*representative x i) := by
    change Real.sin (2*Real.pi*representative (torusCoordinatePermute (Equiv.swap 0 i) x) 0)=_
    rw [representative_coordinatePermute,sibling_coverCoordinatePermute_apply,Equiv.swap_apply_left]
  rcases isMinimizerAt_reflection_strict_normal_sign hV hF hmF hcF hRF
    (e.isNormalMeasure_preimage hE hμ) (e.pullback_contDiff hN) (e.pullback_periodic hp)
    (e.pullback_normal_ae hN hp hae) with hz|hn|hpos
  · left
    intro x hx
    have hh := hz (e.torus x) (hpoint x hx)
    dsimp only [e] at hh
    change (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0=0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh
  · right; left
    intro x hx hs
    have hh := hn (e.torus x) (hpoint x hx) (by rwa [hseam])
    dsimp only [e] at hh
    change (coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0<0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh
  · right; right
    intro x hx hs
    have hh := hpos (e.torus x) (hpoint x hx) (by rwa [hseam])
    dsimp only [e] at hh
    change 0<(coordinatePermutation (Equiv.swap 0 i)).pullback N
      (representative (torusCoordinatePermute (Equiv.swap 0 i) x)) 0 at hh
    rwa [coordinateSwap_pullback_scalar i hp x] at hh

end CubicTorus
end
end
end
end OAI
