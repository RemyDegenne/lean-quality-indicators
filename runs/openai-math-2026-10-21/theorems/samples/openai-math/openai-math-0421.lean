namespace OAI

noncomputable section

open scoped ComplexOrder

open Filter Topology

open Filter Topology Metric

open Filter Topology MeasureTheory

open scoped RealInnerProductSpace ENNReal

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal

open MeasureTheory ProbabilityTheory

open MeasureTheory Filter Topology

open scoped ComplexOrder BoundedContinuousFunction

open MeasureTheory Filter Topology TopologicalSpace

open MeasureTheory ProbabilityTheory Filter Topology

namespace HochschildRare

variable {X : Type*} [MeasurableSpace X]

variable (ν : Measure X) [IsProbabilityMeasure ν]

lemma label_collision_mass_le {I J : Type*} [Fintype I] [Fintype J]
    (A : J → Set X) :
    (Measure.pi (fun _ : I => ν)).real
      {w | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ≤
      ((Fintype.card I).choose 2 : ℝ) * ∑ a : J, ν.real (A a)^2 := by
  classical
  let Z := (Finset.univ : Finset I).powersetCard 2
  let E (s : Finset I) (a : J) := {w : I → X | ∀ i ∈ s, w i ∈ A a}
  have hsub : {w : I → X | ∃ i j : I, i ≠ j ∧ ∃ a : J, w i ∈ A a ∧ w j ∈ A a} ⊆
      ⋃ s ∈ Z, ⋃ a : J, E s a := by
    rintro w ⟨i,j,hij,a,hi,hj⟩
    refine Set.mem_iUnion.mpr ⟨{i,j},Set.mem_iUnion.mpr ⟨?_,Set.mem_iUnion.mpr ⟨a,?_⟩⟩⟩
    · simp [Z,Finset.mem_powersetCard,hij]
    · intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
  calc
    _ ≤ (Measure.pi (fun _ : I => ν)).real (⋃ s ∈ Z, ⋃ a : J, E s a) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ s ∈ Z, (Measure.pi (fun _ : I => ν)).real (⋃ a : J, E s a) :=
      measureReal_biUnion_finset_le Z _
    _ ≤ ∑ s ∈ Z, ∑ a : J, (Measure.pi (fun _ : I => ν)).real (E s a) := by
      gcongr with s hs
      exact measureReal_iUnion_fintype_le _
    _ = _ := by
      have hc (s : Finset I) (hs : s ∈ Z) : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
      simp_rw [E,finite_coordinates_mass]
      rw [Finset.sum_congr rfl (fun s hs => by rw [hc s hs])]
      simp [Z,Finset.card_powersetCard,nsmul_eq_mul]

end HochschildRare
end
end OAI
