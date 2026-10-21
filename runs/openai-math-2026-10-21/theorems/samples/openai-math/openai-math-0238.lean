namespace OAI

open scoped ContDiff ZeroAtInfty NNReal

namespace DefocusingNLS

open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousLinearizedStep

section

variable (n : ℕ) (z : ProfileCertificate.ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < k)
    (q : HomogeneousY (radialShootingA n) k)
    (hq : ∀ y, homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk q y =
      radialMatchedCartesian n z y)

local notation "a" => radialShootingA n

local notation "b" => radialShootingB (profileMatchingParameter z)

local notation "m" => n + radialInnerShootingThreshold

local notation "Q" => radialMatchedCartesian n z

local notation "S" => homogeneousLinearizedStep a b k ha ha1 hk m q

include hX hz

include hq

theorem radialMatched_translation_evolution (v : E) (u : HomogeneousY a k)
    (hu : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk u y = cartesianDerivative v Q y)
    (s : ℝ≥0) : S s u = Real.exp ((1 / 2 : ℝ) * s) • u := by
  obtain ⟨uH, hH⟩ := homogeneous_profile_directional_derivative a (k + 2) ha ha1
    (by linarith) Q (radialMatchedCartesian_contDiff n z hX hz) (symbol n z hX hz) v
  apply homogeneousLinearized_eigenvector_of_physical a b k ha ha1 hk m q u uH (1 / 2)
    (fun x => (hH x).trans (hu x).symm)
  intro x
  rw [show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) = Q from funext hq,
    show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) =
      cartesianDerivative v Q from funext hu]
  simpa only [hu, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    radialMatched_translationMode n z hX hz v x

end
end DefocusingNLS
end OAI
