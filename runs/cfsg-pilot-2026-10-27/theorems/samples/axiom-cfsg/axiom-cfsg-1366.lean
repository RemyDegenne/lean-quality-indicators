public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.exists_z (c : Core3Ctx T M H K1 L M₁) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ (∀ t ∈ T, t * z = z * t) ∧
      Lemma115Hyp (g0Of T M H K1) (sOf T K1) (mcOf T) z ∧ oddCoreIn (g0Of T M H K1) = ⊥ := by
  obtain ⟨z, hz, hz1, hz2, hzc, hZ⟩ := exists_generator c.st
  have h115 := lemma115Hyp_g0 c.st c.pCore_ne c.inM c.sylow hz hz1 hz2 hzc hZ
  have hYG0 : yOfL22 T M ≤ g0Of T M H K1 := yOfL22_le_g0Of T M H K1
  exact ⟨z, hz, hz1, hz2, hzc, h115,
    oddCoreIn_g0_eq_bot c.st hYG0 hz hz1 h115.inverts_oddCoreIn⟩

end S1421
end CFSG.Quasithin
end
