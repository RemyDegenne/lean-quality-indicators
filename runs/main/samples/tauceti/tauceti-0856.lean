public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap (polar polar_smul_left)

section Noncompact

variable {K V : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

theorem not_isCompact_orthogonalGroup (hiso : ¬Q.Anisotropic) :
    ¬IsCompact (orthogonalGroup Q : Set (V ≃ₗ[K] V)) := by
  by_cases hQ : Q.radical = ⊥
  · obtain ⟨u, v, -, hu, hv, huv⟩ :=
      _root_.QuadraticMap.exists_isotropic_pair_of_radical_eq_bot hQ hiso
    exact not_isCompact_of_hyperbolicPairTorus_sq_mem Q hu hv huv fun t =>
      (hyperbolicPairTorus Q hu hv huv (t ^ 2)).2
  intro hcpt
  -- Scale a nonzero radical vector while fixing the kernel of a linear functional.
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  obtain ⟨f, hfu⟩ := Module.Projective.exists_dual_eq_one K hu0
  let φ : Module.End K V →ₗ[K] K := f.comp (LinearMap.applyₗ u)
  have hF : Continuous fun g : V ≃ₗ[K] V => φ g :=
    (IsModuleTopology.continuous_of_linearMap φ).comp continuous_linearEquiv_toLinearMap
  obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp (hcpt.image hF).isBounded
  obtain ⟨t, ht⟩ := NormedField.exists_lt_norm K (max r 1)
  have ht0 : t ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (le_max_right r 1) |>.trans ht)
  let g := LinearEquiv.dilatransvection (f := f) (v := (t - 1) • u)
    (by simpa [hfu] using isUnit_iff_ne_zero.mpr ht0)
  have hg : g ∈ orthogonalGroup Q := by
    apply mem_orthogonalGroup_iff.mpr
    intro x
    rw [LinearEquiv.dilatransvection.apply]
    have hrad : f x • ((t - 1) • u) ∈ Q.radical :=
      Q.radical.smul_mem _ (Q.radical.smul_mem _ hu)
    simpa [add_comm] using (_root_.QuadraticMap.mem_radical_iff'.mp hrad).2 x
  have hgφ : φ g = t := by simp [φ, g, LinearMap.transvection.apply, hfu]
  have hbound : ‖φ g‖ ≤ r := hr _ ⟨g, hg, rfl⟩
  rw [hgφ] at hbound
  exact (not_le_of_gt ht) (le_trans hbound (le_max_left r 1))

end Noncompact
end QuadraticMap
end TauCeti
end
