public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank

open CFSG.ClassicalInvolution.Models.SymplecticPairs

open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)

open CFSG.LieType.CurtisTits (rankOne levi)

open CFSG.Quasithin (perfectCore)

open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

open CFSG.SeitzReduction.UnitaryPilot (modelToG)

theorem eq_of_rootTorusHom_of_tau {K : Type} [Field K] {N : ℕ} {G : Type*} [Group G]
    (φ ψ : StatedSp N K →* G)
    (hτ : ∀ (j : Fin N) (hj : j.val + 1 < N) (κ : Kˣ),
      φ (diagSp K N (Pi.mulSingle j κ * Pi.mulSingle ⟨j.val + 1, hj⟩ κ⁻¹)) =
        ψ (diagSp K N (Pi.mulSingle j κ * Pi.mulSingle ⟨j.val + 1, hj⟩ κ⁻¹)))
    (hlast : ∀ j : Fin N, j.val + 1 = N → ∀ κ : Kˣ,
      φ (rootTorusHom K N j κ) = ψ (rootTorusHom K N j κ))
    (k : Fin N) (κ : Kˣ) : φ (rootTorusHom K N k κ) = ψ (rootTorusHom K N k κ) := by
  obtain ⟨d, hd⟩ : ∃ d, d = N - 1 - k.val := ⟨_, rfl⟩
  induction d generalizing k with
  | zero => exact hlast k (by have := k.2; omega) κ
  | succ d ih =>
    have hk1 : k.val + 1 < N := by omega
    have hsplit : rootTorusHom K N k κ = diagSp K N (Pi.mulSingle k κ *
        Pi.mulSingle ⟨k.val + 1, hk1⟩ κ⁻¹) * rootTorusHom K N ⟨k.val + 1, hk1⟩ κ := by
      rw [rootTorusHom_apply, rootTorusHom_apply, ← map_mul, mul_assoc, ← Pi.mulSingle_mul,
        inv_mul_cancel, Pi.mulSingle_one, mul_one]
    rw [hsplit, map_mul φ, map_mul ψ, hτ k hk1 κ, ih ⟨k.val + 1, hk1⟩ (by simp only; omega)]

end CFSG.SeitzReduction.SymplecticPilot
end
