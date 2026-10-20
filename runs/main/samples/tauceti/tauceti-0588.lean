public section

namespace TauCeti

open LieAlgebra LieModule Module TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

local notation "U" => _root_.UniversalEnvelopingAlgebra K L

section FiniteDimensional

variable [IsAlgClosed K] [FiniteDimensional K M] (b : (IsKilling.rootSystem H).Base)

variable (M) in
theorem iSup_centerEigenspace_vermaCentralCharacter_eq_top :
    ⨆ lam : {l : Dual K H // IsDominantIntegral b l},
      centerEigenspace K L M (vermaCentralCharacter b lam.1) = ⊤ := by
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible_of_isKilling K L M
  -- each irreducible summand is a copy of some `L(lam)`, so it lies in `M_{chi_lam}`
  have hN (i : Fin k) : N i ≤ ⨆ lam : {l : Dual K H // IsDominantIntegral b l},
      centerEigenspace K L M (vermaCentralCharacter b lam.1) := by
    have := hirr i
    obtain ⟨lam, hlam, e⟩ :=
      exists_isDominantIntegral_nonempty_lieModuleEquiv_irreducibleQuotient (M := N i) b
    exact le_iSup_of_le ⟨lam, hlam⟩ (le_centerEigenspace_of_nonempty_lieModuleEquiv e)
  exact top_unique <| LieSubmodule.iSup_toSubmodule_eq_top.mp hint.submodule_iSup_eq_top ▸
    iSup_le hN

end FiniteDimensional
end TauCeti
end
