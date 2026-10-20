namespace P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd

attribute [-instance] ModularCurve.PDPairing.isFreeGroup_inf ModularCurve.PDPairing.instFintypeCusp ModularCurve.PDPairing.iotaDeg0_range_finiteIndex ModularCurve.PDPairing.CentralExt.instInv ModularCurve.PDPairing.CentralExt.instGroup ModularCurve.PDPairing.CentralExt.instMul ModularCurve.PDPairing.CentralExt.instOne ModularCurve.PDPairing.Gamma0Upper_finiteIndex ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper CohCarrier.GammaHLower_finiteIndex

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace MapsDvdSol

section Pairing

p2m_open

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
  (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪))
  (N q : ℕ) [NeZero N] [NeZero q]
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)

include hp hp2 hpu

omit hp hp2 hpu in

theorem opFamily_comm (S : Set ℕ) (g g' : Gen N S) :
    opFamily N ⊤ S 𝒪 g * opFamily N ⊤ S 𝒪 g' = opFamily N ⊤ S 𝒪 g' * opFamily N ⊤ S 𝒪 g := by

  have key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime),
      (haveI : NeZero a := ⟨ha.ne_zero⟩; haveI : NeZero b := ⟨hb.ne_zero⟩;
        heckeTL N ⊤ 𝒪 a * heckeTL N ⊤ 𝒪 b = heckeTL N ⊤ 𝒪 b * heckeTL N ⊤ 𝒪 a) := by
    intro a b ha hb
    haveI : NeZero a := ⟨ha.ne_zero⟩
    haveI : NeZero b := ⟨hb.ne_zero⟩
    by_cases hab : a = b
    · subst hab; rfl
    · apply LinearMap.ext
      intro φ
      exact heckeT_comm_of_prime N ⊤ a b ha ((Nat.coprime_primes ha hb).mpr hab) φ
  rcases g with ⟨ℓ, hℓ, hℓS, hℓN⟩ | ⟨r, hr, hrN⟩ | ⟨d⟩ <;>
    rcases g' with ⟨ℓ', hℓ', hℓS', hℓN'⟩ | ⟨r', hr', hrN'⟩ | ⟨d'⟩ <;>
    simp only [opFamily, diamondL_top_eq_one, one_mul, mul_one]
  · exact key ℓ ℓ' hℓ hℓ'
  · exact key ℓ r' hℓ hr'
  · exact key r ℓ' hr hℓ'
  · exact key r r' hr hr'

end Pairing
end MapsDvdSol
end P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd
