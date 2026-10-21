namespace OAI

noncomputable section

open Set Manifold Bundle

open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing

open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector

local instance nonlinearErrorFiberNormed : NormedAddCommGroup TensorFiber := inferInstance

local instance nonlinearErrorFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance nonlinearErrorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

local instance nonlinearErrorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

local instance nonlinearErrorSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)

local instance nonlinearErrorSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

lemma phaseAtlasRemainder_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {B : JetPolynomial.Base → PhaseMean.Tensor} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (A.phaseAtlasRemainder i F e U ℓ L z P B) := by
  have hbase := (A.jetChartMap_smooth i hF).comp hi
  have hV := spaceCoordinates.contDiff.comp
    (finiteAnsatz_smooth_global ((A.vectorChartRead_smooth i hF).comp hi) U hK hKO
      (fun j x _ hx => hzero j x hx) ℓ L z)
  have hm (f : JetPolynomial.Base → JetPolynomial.Space) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun y => RealModes.realMetricTensor (f ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry y)) :=
    (contDiffOn_univ.mp (RealModes.contDiffOn_realMetricTensor isOpen_univ
      (hf.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)).comp planeCoordinateIsometry.contDiff
  have hh := (((hm _ hV).sub (hm _ hbase)).sub
    ((coordinatePolynomialValue_smooth hP hbase z).comp planeCoordinateIsometry.contDiff)).sub hB
  convert hh using 1
  funext y
  simp only [phaseAtlasRemainder,coordinateMetricMap,Pi.add_apply,Function.comp_apply,Function.comp_assoc]
  rw [sub_add_eq_sub_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing
end
end OAI
