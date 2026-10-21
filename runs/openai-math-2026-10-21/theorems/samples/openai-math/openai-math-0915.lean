namespace OAI

noncomputable section

open scoped BigOperators Topology

open Filter

attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

theorem first_collision_dyadic_blocks : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ, 1 ≤ i → i ≤ R x H → L x H < m x → R x H < L x H →
    ∀ t y : ℝ, ∀ q ∈ firstCollisionPairs x H t i,
    y/2 < (prefixDenominator (tupleSuffix q.1 i) : ℝ) →
    (prefixDenominator (tupleSuffix q.1 i) : ℝ) ≤ y →
    GoodCollisionBlock x t H i y q ∧
    (87/100 : ℝ)*fordBandScale x i ≤ B y ∧ B y ≤ (113/100 : ℝ)*fordBandScale x i := by
  filter_upwards [collision_suffix_dyadic_size,eventually_collision_indices,
    eventually_tail_cut_separated] with H hsize hind hsep
  filter_upwards [hsize,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro i hi hiR hL hR t y q hq hlo hhi
  obtain ⟨hl,hr,hv,hfirst,hcommon⟩ := firstCollisionPairs_data (by omega) hq
  have hiL : i+2 ≤ L x H := by unfold R L at *; omega
  have hk : collisionLastIndex x i < L x H := (hind x hm i hiR).2.2
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have hsame : prefixDenominator (tupleSuffix q.1 i)=prefixDenominator (tupleSuffix q.2 i) :=
    firstCollisionSuffixes_equal_value (by omega) hiR (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hdleft := tupleSuffix_denominator_positive hl.1 hL hR hi hiR
  have hdright := tupleSuffix_denominator_positive hr.1 hL hR hi hiR
  have hls := hx i hi hiR hiL hL _ (chosenRemainder_spec hl.1.2.2.1).1 y
    (by rwa [← hdleft]) (by rwa [← hdleft])
  have hrs := hx i hi hiR hiL hL _ (chosenRemainder_spec hr.1.2.2.1).1 y
    (by rwa [← hdright,← hsame]) (by rwa [← hdright,← hsame])
  refine ⟨⟨hl,hr,hv,hfirst,hcommon,?_,?_,?_,?_⟩,hls.2.1,hls.2.2⟩
  · simpa only [wholeWitnessPrime,ite_eq_right (by omega : i ≠ 0)] using hls.1
  · simpa only [wholeWitnessPrime,ite_eq_right (by omega : i ≠ 0)] using hrs.1
  · rwa [← tupleSuffix_denominator_block hl.1 hL hR hi hiR hik hk]
  · intro hzero
    omega

end TotientAsymptotic
end
end OAI
