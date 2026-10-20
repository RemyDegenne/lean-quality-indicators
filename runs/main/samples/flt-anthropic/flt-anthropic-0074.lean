namespace P2MW.S_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

namespace HeckeEis

p2m_open

namespace Sh1

open CongruenceSubgroup Matrix ModularCurve Sh1t Function

open scoped MatrixGroups

variable (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N) (K : Type*) [CommRing K]

variable (σ : (ProjectiveLine (ZMod p)) → Gamma0 N) (hσ : ∀ P : (ProjectiveLine (ZMod p)), act N p (σ P) (infty p) = P)

theorem zOf_mem_coeffCocycles (φ : Additive (Gamma0 (N * p)) →+ K) : zOf N p hpN K σ hσ φ ∈ coeffCocycles (rho N p K) := by
  intro g h
  funext P
  rw [Pi.add_apply, rho_apply, zOf_apply, zOf_apply, zOf_apply, kappa_mul, ofMul_mul, map_add]

end Sh1
end HeckeEis
end
end P2MW.S_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero
