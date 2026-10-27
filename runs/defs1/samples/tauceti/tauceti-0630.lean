public section

open AddSubgroup

namespace TauCeti.FiniteQuadraticModule

/-- Odd coefficients congruent modulo eight give isometric cyclic dyadic quadratic forms
at every positive exponent. -/
noncomputable def dyadicCyclicIsometryOfModEqEight (k : ℕ) [NeZero k] {θ η : ℤ}
    (hθ : Odd θ) (h : θ ≡ η [ZMOD 8]) : Isometry (dyadicCyclic k θ) (dyadicCyclic k η) :=
  Classical.choice <| by
    have hη : Odd η := by
      obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp h
      obtain ⟨s, hs⟩ := hθ
      refine ⟨s + 4 * d, ?_⟩
      omega
    obtain ⟨u, hu⟩ := ZMod.exists_unit_sq_mul_intCast_eq_of_modEq_eight k hη h
    let v := ZMod.unitsMap (pow_dvd_pow 2 k.le_succ) u
    have hv : ((v.val.val : ℤ) : ZMod (2 ^ k)) =
        ((u.val.val : ℤ) : ZMod (2 ^ k)) := by
      simp [v, ZMod.unitsMap, ZMod.castHom_apply]
    have hq := congrArg (dyadicCyclic k η).quadratic hv
    rw [dyadicCyclic_quadratic_intCast, dyadicCyclic_quadratic_intCast] at hq
    -- Equal residue representatives give equal cyclic values. The public value
    -- formula lifts this equality back to the common dyadic modulus.
    have hlift : ((η * (v.val.val : ℤ) ^ 2 : ℤ) : ZMod (2 ^ (k + 1))) =
        ((η * (u.val.val : ℤ) ^ 2 : ℤ) : ZMod (2 ^ (k + 1))) := by
      apply (ZMod.toRatAddCircle_injective (2 ^ (k + 1))).eq_iff.mp
      rw [ZMod.toRatAddCircle_intCast, ZMod.toRatAddCircle_intCast]
      push_cast
      exact hq
    refine (nonempty_isometry_dyadicCyclic_iff θ η).mpr ⟨v, ?_⟩
    rw [hlift]
    push_cast
    simpa only [ZMod.natCast_zmod_val] using hu.symm

end TauCeti.FiniteQuadraticModule
end
