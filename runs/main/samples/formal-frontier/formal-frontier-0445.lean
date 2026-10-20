@[expose] public section

open Filter

universe u v

namespace Ideal

theorem eq_pi_map_evalRingHom_of_isClosed
    {ι : Type u} {R : ι → Type v} [∀ i, Semiring (R i)]
    [∀ i, TopologicalSpace (R i)] (I : Ideal (∀ i, R i))
    (hI : IsClosed (I : Set (∀ i, R i))) :
    I = Ideal.pi (fun i ↦ I.map (Pi.evalRingHom R i)) := by
  ext x
  rw [mem_pi]
  constructor
  · intro hx i
    exact mem_map_of_mem (Pi.evalRingHom R i) hx
  · intro hx
    have hlift (i : ι) : ∃ y : ∀ i, R i, y ∈ I ∧ y i = x i := by
      simpa only [mem_map_iff_of_surjective (Pi.evalRingHom R i)
        (Function.surjective_eval i), Pi.evalRingHom_apply] using hx i
    choose y hyI hy using hlift
    classical
    let trunc : Finset ι → (∀ i, R i) := fun s ↦
      ∑ i ∈ s, Pi.single i 1 * y i
    apply hI.mem_of_tendsto (f := trunc) (b := atTop)
    · apply tendsto_pi_nhds.2
      intro i
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_finset_mem_atTop i] with s his
      simp only [trunc, Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simpa using hy i
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji.symm]
      · simp [his]
    · exact Eventually.of_forall fun s ↦
        I.sum_mem fun i _ ↦ I.mul_mem_left (Pi.single i 1) (hyI i)

end Ideal
end
