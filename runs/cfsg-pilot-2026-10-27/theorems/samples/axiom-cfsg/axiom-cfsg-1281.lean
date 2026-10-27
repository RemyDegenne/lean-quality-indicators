public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank

theorem ker_restrict_eq_pPrimeCore {C : Type*} [Group C] [Finite C] {L : Subgroup C}
    (hL : L.IsSubnormal) :
    ((QuotientGroup.mk' (pPrimeCore 2 C)).comp L.subtype).ker = pPrimeCore 2 ↥L := by
  set N : Subgroup C := pPrimeCore 2 C with hN
  apply le_antisymm
  · set ker := ((QuotientGroup.mk' N).comp L.subtype).ker with hker
    have hnorm : ker.Normal := MonoidHom.normal_ker _
    have hcop : Nat.Coprime 2 (Nat.card ker) := by
      have hmem : ∀ y : ker, ((y : L) : C) ∈ N := by
        intro y
        have := y.2
        rw [MonoidHom.mem_ker] at this
        exact (QuotientGroup.eq_one_iff _).mp this
      have hinj : Function.Injective (fun y : ker => (⟨((y : L) : C), hmem y⟩ : N)) := by
        intro a b hab
        have := congrArg (fun z : N => (z : C)) hab
        exact Subtype.ext (Subtype.ext this)
      have hdvd : Nat.card ker ∣ Nat.card N := by
        refine Subgroup.card_dvd_of_injective
          ({ toFun := fun y : ker => (⟨((y : L) : C), hmem y⟩ : N)
             map_one' := rfl
             map_mul' := fun _ _ => rfl } : ker →* N) hinj
      exact Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card
    exact le_sSup ⟨hnorm, hcop⟩
  · intro l hl
    have h1 : (l : C) ∈ pPrimeCoreOf 2 L := ⟨l, hl, rfl⟩
    have h2 := pPrimeCoreOf_le_of_subnormal 2 hL h1
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr h2

end CFSG.GH74.GLS
end
