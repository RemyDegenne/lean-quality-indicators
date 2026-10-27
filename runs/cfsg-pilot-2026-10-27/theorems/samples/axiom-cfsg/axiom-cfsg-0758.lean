public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed
  CFSG.LieType.Simplicity

theorem exists_surjective_fixedGroup_twistedE6RootGroup {k : Type} [Field k] [Finite k]
    [CharP k 2] {n : ℕ} (hn : 1 ≤ n) (θ : k →+* k) (hk : Nat.card k = (2 ^ n) ^ 2)
    (hθ : ∀ c, θ c = c ^ (2 ^ n)) :
    ∃ σ : k ≃+* k, σ.toRingHom = θ ∧
      ∃ π : ↥(fixedGroup k θ) →* ↥(twistedE6RootGroup k σ),
        Function.Surjective π ∧ π.ker = Subgroup.center ↥(fixedGroup k θ) := by
  obtain ⟨σ, hσθ⟩ := exists_ringEquiv_eq_pow_two_pow hθ
  have hθinv : ∀ c, θ (θ c) = c := theta_theta_of_card hk hθ
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := fun c => by
    rw [show σ c = σ.toRingHom c from rfl, hσθ]
    exact hθ c
  have h2n : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
  have hK4 : 4 ≤ Nat.card k := by
    rw [hk]
    nlinarith
  have hθ' : ∀ c, (σ.toRingHom) ((σ.toRingHom) c) = c := fun c => by
    rw [hσθ]
    exact hθinv c
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (p := 2) (f := n)
      Nat.prime_two hn k hk σ hσ
  rw [hσθ] at hder
  let π : ↥(fixedGroup k θ) →* ↥(twistedE6RootGroup k σ) :=
    (MulEquiv.subgroupCongr hder).toMonoidHom.comp (twistedIsogeny θ hθinv hK4)
  have hker : π.ker = (twistedIsogeny θ hθinv hK4).ker := by
    ext x
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      exact (MulEquiv.subgroupCongr hder).injective (by simpa using h)
    · intro h
      simpa using congrArg (MulEquiv.subgroupCongr hder) h
  refine ⟨σ, hσθ, π, ?_, ?_⟩
  · exact (MulEquiv.subgroupCongr hder).surjective.comp (twistedIsogeny_surjective θ hθinv hK4)
  · rw [hker, ker_twistedIsogeny_eq_center (θ := θ) hθinv hK4]

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
end
