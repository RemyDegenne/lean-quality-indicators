@[expose] public section

open TauCeti.DavisKahan.Angle

open TauCeti.DavisKahan.Sylvester

open TauCeti.DavisKahan.TanTheta

namespace TauCeti

namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahanExt

open TauCeti.DavisKahan

open TauCeti.DavisKahan.ExactSinTheta

open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation

open TauCeti.DavisKahan.TanTheta

open TauCeti.DavisKahan.TanTheta

open TauCeti.RealComplexification

open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable {Z V : Submodule ℝ E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

variable [CompleteSpace Z]

theorem theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E)
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℝ] E,
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  theorem6_3_ideal_infiniteData_exists_real N (Theorem63TrialData.ofUnbounded D V) hdelta
    hCompression
    (fun z => by
      simpa using crossed_lower_of_reducing (𝕜 := ℝ) A D V hVdom hVcomm
        (fun y hy hydom => by simpa using hUnwanted y hy hydom) z)
    hResidual

end
end DavisKahan1970
end TauCeti
end
