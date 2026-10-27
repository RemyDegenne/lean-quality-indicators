public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG
  CFSG.LocalAnalysis.ComponentInitial

open scoped commutatorElement

namespace Gen

theorem odd_mem_pPrimeCore_of_mem_Op {X : Type*} [Group X] [Finite X] {x : X}
    (hx : x ∈ Op_p'p 2 X) (hodd : Odd (orderOf x)) : x ∈ pPrimeCore 2 X := by
  have h1 : QuotientGroup.mk' (pPrimeCore 2 X) x ∈ pCore 2 (X ⧸ pPrimeCore 2 X) := hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 pCore_isPGroup ⟨_, h1⟩
  have hk' : orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x) = 2 ^ k := by
    have : orderOf (⟨QuotientGroup.mk' (pPrimeCore 2 X) x, h1⟩ :
        ↥(pCore 2 (X ⧸ pPrimeCore 2 X))) = 2 ^ k := by simpa using hk
    rwa [Subgroup.orderOf_mk] at this
  have hdvd : orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x) ∣ orderOf x := orderOf_map_dvd _ x
  have hodd' : Odd (orderOf (QuotientGroup.mk' (pPrimeCore 2 X) x)) := Odd.of_dvd_nat hodd hdvd
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk'] at hodd'
    exact (Nat.not_even_iff_odd.2 hodd') (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk'
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 hk')

end Gen
end CFSG.GH74.Uniqueness.SU.SU7
end
