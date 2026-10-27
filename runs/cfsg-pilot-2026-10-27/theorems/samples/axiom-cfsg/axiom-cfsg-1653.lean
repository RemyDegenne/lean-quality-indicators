public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup QuaternionGroup

theorem exists_hom_quat {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hH : Nat.card H = 1000) (hN : Nat.card N = 125) (ψ : QuaternionGroup 2 →* H)
    (hψ : Function.Injective ψ) : ∃ ρ : H →* QuaternionGroup 2, ρ.ker = N := by
  set f : QuaternionGroup 2 →* H ⧸ N := (QuotientGroup.mk' N).comp ψ with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : ψ x ∈ N := by
      have : ψ x ∈ (QuotientGroup.mk' N).ker := hx
      rwa [QuotientGroup.ker_mk'] at this
    have h1 : orderOf (ψ x) ∣ 125 := hN ▸ Subgroup.orderOf_dvd_natCard N hxN
    have h2 : orderOf x ∣ 8 := card_quat2 ▸ orderOf_dvd_natCard x
    rw [orderOf_injective ψ hψ x] at h1
    have h3 : orderOf x ∣ Nat.gcd 8 125 := Nat.dvd_gcd h2 h1
    have h4 : orderOf x = 1 := by
      have : Nat.gcd 8 125 = 1 := by norm_num
      rw [this] at h3
      exact Nat.dvd_one.1 h3
    exact orderOf_eq_one_iff.1 h4
  have hcard : Nat.card (H ⧸ N) = 8 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hH, hN] at this
    omega
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, card_quat2])
  let e : QuaternionGroup 2 ≃* H ⧸ N := MulEquiv.ofBijective f hbij
  refine ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' N), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    QuotientGroup.mk'_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

end CFSG.EvenSporadicStandard.RuStd.S2
end
