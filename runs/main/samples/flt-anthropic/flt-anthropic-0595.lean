namespace P2MW.S_AlgebraicCurve_tateCommFinite

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 6400000

set_option maxHeartbeats 12800000

section

section

section

section

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 3200000

set_option linter.unusedSectionVars false

noncomputable section

p2m_open

p2m_open

namespace ModularCurve

namespace KwF4R1V410a

p2m_open

scoped instance kwF4R1V410a_subsingletonHeightOneSpectrumDVR
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Subsingleton (HeightOneSpectrum O) :=
  ⟨fun a b => IsDedekindDomain.HeightOneSpectrum.ext
    (((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      inferInstance).2.unique ⟨a.3, a.2⟩ ⟨b.3, b.2⟩)⟩

section Bridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring

local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring

local notation "O_W" => w.adicCompletionIntegers

local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

theorem kwF4R1V410a_exists_sub_mem_completionIdeal_pow (n : ℕ) (y : O_W) :
    ∃ x : O_w, y - algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n := by

  have hball_open : IsOpen {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} :=
    (adicCompletion.isOpen_setOf_valued_le F w.heightOneSpectrum
      WithZero.exp_ne_zero).preimage (continuous_sub_right y.val)
  have hy_mem : y.val ∈ {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.mem_setOf_eq, sub_self, _root_.map_zero]; exact WithZero.zero_le _
  have hmeet := mem_closure_iff.mp
    ((denseRange_algebraMap F w.heightOneSpectrum) y.val) _ hball_open hy_mem

  have hexists : ∃ z : F, Valued.v (algebraMap F w.adicCompletion z - y.val)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hmeet with ⟨z₀, hz₀_ball, z, hz_eq⟩
    exact ⟨z, hz_eq ▸ hz₀_ball⟩
  obtain ⟨z, hz⟩ := hexists
  rw [show algebraMap F w.adicCompletion z = ((z : F) : w.adicCompletion) from rfl] at hz

  have hz_val_le : w.heightOneSpectrum.valuation F z ≤ 1 := by
    have hzhat : Valued.v ((z : w.adicCompletion)) ≤ (1 : ℤᵐ⁰) := by
      calc Valued.v ((z : w.adicCompletion))
          = Valued.v (((z : w.adicCompletion) - y.val) + y.val) := by ring_nf
        _ ≤ max (Valued.v ((z : w.adicCompletion) - y.val)) (Valued.v y.val) :=
            Valuation.map_add _ _ _
        _ ≤ (1 : ℤᵐ⁰) := max_le
            (hz.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)))
            y.2
    rwa [valuedAdicCompletion_eq_valuation'] at hzhat
  have hz_mem : z ∈ (O_w : ValuationSubring F) := by
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one F z
      (fun v' => by
        obtain rfl : v' = w.heightOneSpectrum := Subsingleton.elim _ _
        exact hz_val_le)
    exact hr ▸ r.2
  refine ⟨⟨z, hz_mem⟩, ?_⟩
  rw [adicCompletion.mem_completionIdeal_pow, ← WithZero.exp_eq_coe_ofAdd]
  have hsub : (y - algebraMap (O_w) (O_W) ⟨z, hz_mem⟩ : O_W).val
      = y.val - ((z : F) : w.adicCompletion) := rfl
  rw [hsub, Valuation.map_sub_swap]
  exact hz

end Bridge
end KwF4R1V410a
end ModularCurve
end
end
end
end
end
end P2MW.S_AlgebraicCurve_tateCommFinite
