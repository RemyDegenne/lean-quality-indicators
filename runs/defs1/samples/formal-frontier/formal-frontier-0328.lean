@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Coefficients in `R ⧸ I` of the positive successive principal-unit layer,
relative to the supplied generator `π` of a nonzero ideal in the Jacobson
radical. On the original-ring unit `1 + a * π ^ n` the coordinate is `[a]`.
This is the principal-ideal coefficient form of Fesenko–Vostokov, I.(5.4)(3). -/
noncomputable def principalUnitsPowQuotientEquiv [IsDomain R] (I : Ideal R)
    (hI : I ≠ ⊥)
    (hJ : I ≤ Ideal.jacobson ⊥) (π : R) (hgen : I = Ideal.span {π})
    (n : ℕ) (hpos : 1 ≤ n) :
    MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ (I ^ n : Ideal R)) ⧸
        ((I ^ n).principalUnitsToQuotient (I ^ (n + 1)) (by
          rw [← pow_mul]
          exact Ideal.pow_le_pow_right (by
            simpa only [Nat.mul_two] using Nat.add_le_add_left hpos n))).ker ≃*
      Multiplicative (R ⧸ I) := by
  classical
  let h : I.IsPrincipal := ⟨π, hgen⟩
  let g : R := h.principal.choose
  have hg : I = Ideal.span {g} := h.principal.choose_spec
  have hw : ∃ w : Rˣ, π = (w : R) * g := by
    obtain ⟨w, hw⟩ :=
      Ideal.span_singleton_eq_span_singleton.mp (hg.symm.trans hgen)
    exact ⟨w, hw.symm.trans (mul_comm g (w : R))⟩
  let w : Rˣ := hw.choose
  have hden :
      Submodule.comap (I ^ n : Ideal R).subtype (I ^ (n + 1)) =
        (I • ⊤ : Submodule R (I ^ n : Ideal R)) := by
    ext x
    change (x : R) ∈ I ^ (n + 1) ↔
      x ∈ (I • ⊤ : Submodule R (I ^ n : Ideal R))
    rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']
  let transport := Submodule.quotEquivOfEq _ _ hden
  let e := Ideal.quotEquivPowQuotPowSucc h hI n
  let wbar : (R ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom w
  -- Since π = (w : R) * g, the g-coordinate is the π-coordinate times wbar ^ n.
  -- Rescaling uses a residue unit, not an inverse of an arbitrary coefficient.
  let rescale : (R ⧸ I) ≃ₗ[R ⧸ I] (R ⧸ I) :=
    LinearEquiv.smulOfUnit (wbar⁻¹ ^ n)
  have hsq : (I ^ n) ^ 2 ≤ I ^ (n + 1) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by
      simpa only [Nat.mul_two] using Nat.add_le_add_left hpos n)
  have hJac : I ^ n ≤ Ring.jacobson R := by
    rw [← Ideal.jacobson_bot]
    exact (Ideal.pow_le_self
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hpos))).trans hJ
  exact ((I ^ n).principalUnitsQuotientEquiv (I ^ (n + 1)) hsq hJac).trans
    (AddEquiv.toMultiplicative
      ((transport.trans e.symm).toAddEquiv.trans rescale.toAddEquiv))

end Ideal
end
