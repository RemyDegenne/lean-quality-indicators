namespace P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep

set_option autoImplicit false

namespace TwistMain

open CongruenceSubgroup HeckeEis

open scoped MatrixGroups

section Flag

variable (p : ℕ) [Fact p.Prime] (M : ℕ) (hpM : p ∣ M) (κ : Type*) [Field κ] [CharP κ p]

noncomputable def coordW (k : Fin p) : (ZMod p → κ) →ₗ[κ] κ := (basisW p κ).coord k

end Flag
end TwistMain
end P2MW.S_HeckeEis_exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep
