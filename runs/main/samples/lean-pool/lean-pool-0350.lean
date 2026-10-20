public section

open Finset

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

local instance carlemanCoreCommutatorAlgebraNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreCommutatorAlgebraNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

theorem commutator_pointwise_divergence
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    {z : ParabolicPoint} (hz : z ∈ U) :
    2 * commutatorSymmetric φ v z * commutatorSkew φ v z =
      carlemanCommutatorDensity φ v z +
        timePartial (commutatorTimeFlux φ v) z +
        ∑ i, spatialPartial (commutatorSpaceFlux φ v i) i z := by
  have hr (i j : Fin 3) :
      spatialSecondPartial v i j z = spatialSecondPartial v j i z :=
    spatialSecondPartial_comm_on isOpen_univ hv.contDiffOn
      (Set.mem_univ z) i j
  have hh (i j : Fin 3) :
      spatialSecondPartial φ i j z = spatialSecondPartial φ j i z :=
    spatialSecondPartial_comm_on hU hφ hz i j
  have hQt := timePartial_carlemanPotential_on hU hφ hz
  have hbi := scalarLaplacian_second_diagonal_on hU hφ hz
  have htime := commutator_time_flux_derivative hU hφ hv hz
  have hspace (i : Fin 3) :=
    commutator_space_flux_derivative hU hφ hv hz i
  have hjet := commutator_jet_identity
    z.2 (v z) (timePartial v z) (timePartial φ z)
    (timePartial (fun y => timePartial φ y) z)
    (scalarLaplacian φ z)
    (scalarGradSq φ z - timePartial φ z)
    (timePartial (fun y => scalarGradSq φ y - timePartial φ y) z)
    (fun i => spatialPartial φ i z)
    (fun i => timePartial (fun y => spatialPartial φ i y) z)
    (fun i => spatialPartial v i z)
    (fun i => timePartial (fun y => spatialPartial v i y) z)
    (fun i => spatialPartial (scalarLaplacian φ) i z)
    (fun i => spatialSecondPartial (scalarLaplacian φ) i i z)
    (fun i j => spatialSecondPartial φ i j z)
    (fun i j => spatialSecondPartial v i j z)
    hr hh rfl hQt rfl
  unfold commutatorSymmetric commutatorSkew carlemanCommutatorDensity
  rw [← hbi, htime]
  simp_rw [hspace]
  simpa only [scalarLaplacian, scalarGradSq] using hjet

end ESS
end
end
