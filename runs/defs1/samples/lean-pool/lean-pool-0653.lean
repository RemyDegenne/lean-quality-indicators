@[expose] public section

namespace Stafford38.Geometry.GeneralTangentLimitCriterion

open Stafford38.Characteristic

open Stafford38.Geometry.AffineConormalClosure

open Stafford38.Geometry.AffineConormalSpan

open Stafford38.Geometry.ConormalScalarExtensionVanishing

open Stafford38.Geometry.LaurentConormalDirection

open Stafford38.Geometry.ProjectiveConormalDehomogenization

open Stafford38.Geometry.ProjectiveConormalDirections

open Stafford38.Geometry.ScalarExtensionPoints

open Stafford38.Geometry.SmoothAffineConormal

open Stafford38.Geometry.SmoothConormalFibreVanishing

open Stafford38.Geometry.FormalDivisorLaurentConormal

open Stafford38.Geometry.GeneralTangentLatticePresentation

open Stafford38.Geometry.LocalizedProjectiveChartTransition

open Stafford38.Geometry.ProjectiveEquationFormalChart

open Stafford38.GeometryPowerSeriesTangentLimit

open Stafford38.GeometryRetractionSpecialization

noncomputable section

variable {k : Type*} [Field k]

/-- The data appearing in the paper's tangent-limit hypothesis, expressed in
the affine chart of the projective arc.  `hposition` says that the generic
projective point belongs to the cone spanned by the generic tangent lattice;
the tangent-space equality is the exact smooth affine tangent dictionary.
The cardinality equation records the advertised rank `dimY + 1`.
-/
structure Input {n dimY : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (I : Ideal (MvPolynomial (Fin n) k))
    (q : Fin (n + 1) → PowerSeries k)
    (B : Matrix (Fin (n + 1)) κ (PowerSeries k)) where
  /-- The affine coordinate axis specifying the tangent-limit residue condition. -/
  axis : Fin n
  /-- A left inverse of the matrix whose columns span the limiting tangent space. -/
  C : Matrix κ (Fin (n + 1)) (PowerSeries k)
  hprime : I.IsPrime
  hsplit : C * B = 1
  hrank : Fintype.card κ = dimY + 1
  hq0 : q 0 ≠ 0
  hbase : ∀ f ∈ I.map (scalarPolynomialMap
      (k := k) (K := LaurentSeries k) (Fin n)),
      MvPolynomial.eval (dehomogenizedPoint (laurentColumn q)) f = 0
  hsmooth : SmoothAffinePoint
      (I.map (scalarPolynomialMap
        (k := k) (K := LaurentSeries k) (Fin n)))
      (dehomogenizedPoint (laurentColumn q))
  hposition : ∃ c : κ → LaurentSeries k, ∀ i,
      laurentColumn q i = ∑ j, algebraMap (PowerSeries k) (LaurentSeries k)
        (B i j) * c j
  htangent : dehomogenizedTangentSpan (laurentColumn q)
      (fun i j ↦ algebraMap (PowerSeries k) (LaurentSeries k) (B i j)) =
      zariskiTangentSpace (dehomogenizedPoint (laurentColumn q))
        (I.map (scalarPolynomialMap
          (k := k) (K := LaurentSeries k) (Fin n)))
  haxis : ∀ j, PowerSeries.constantCoeff (B axis.succ j) = 0

end
end Stafford38.Geometry.GeneralTangentLimitCriterion
end
