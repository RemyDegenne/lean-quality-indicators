namespace OAI

section

noncomputable section

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal

open MeasureTheory Filter Set Module

universe u

open scoped TensorProduct

open Set Module

open MeasureTheory Set

open scoped ENNReal

open IsDiscreteValuationRing IsLocalRing

open scoped ENNReal BigOperators

open MeasureTheory Set IsDiscreteValuationRing

open Filter

open scoped BigOperators Topology

namespace PrimeDegreePackets

open MeasureTheory NumberField IsDiscreteValuationRing

open scoped ENNReal Pointwise nonZeroDivisors

theorem localIdealWeight_eq_model_shell {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, Algebra (PadicInt p) (R i)] [∀ i, TopologicalSpace (R i)]
    [∀ i, IsTopologicalRing (R i)] [∀ i, SecondCountableTopology (R i)] [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (E : completedMaximalOrder (K := K) p ≃ₐ[PadicInt p] ∀ i, R i)
    (hE : Continuous E) (hEs : Continuous E.symm)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hJ : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ 1) :
    localIdealWeight M p J = localShellProbability R (modelUnitProbability p E)
      (modelLocalModule M p E)
      (fun i => (addVal (R i) (E ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩ i)).toNat) := by
  let u : completedMaximalOrder (K := K) p :=
    ⟨idealLocalGenerator p J, integral_idealLocalGenerator p J hJ⟩
  let k : ι → ℕ := fun i => (addVal (R i) (E u i)).toNat
  let := modelUnitProbability_isProbability p E hE
  let := modelUnitProbability_isHaar p E hE
  have hxu : E u ∈ productDVRShell R k := by
    intro i
    exact (ENat.natCast_toNat (addVal_eq_top_iff.not.mpr
      (model_generator_components_ne_zero p E _ _ i))).symm
  obtain ⟨z,hz⟩ := productDVRShell_transitive R k
    (productDVRShell_nonempty R k).choose_spec hxu
  change localIdealWeight M p J = orbitContainmentProbability (modelUnitProbability p E)
    (modelLocalModule M p E) (productDVRShell_nonempty R k).choose
  rw [localIdealWeight, actual_containment_eq_model_orbit M hn p E hE hEs u, ← hz]
  exact orbitContainmentProbability_smul (modelUnitProbability p E)
    (modelLocalModule M p E : Set (∀ i, R i)) _ z

end PrimeDegreePackets
end
end
end OAI
