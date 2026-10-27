public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Blueprint CFSG.Certificates

open CFSG.Sporadic.Mathieu

variable {X : Type} [Group X]

theorem orderOf_mk_eq_two (hZ : Nat.card ↥(Subgroup.center X) = 3) {a : X} (ha : orderOf a = 2) :
    orderOf (QuotientGroup.mk a : X ⧸ Subgroup.center X) = 2 := by
  have h2 : (QuotientGroup.mk a : X ⧸ Subgroup.center X) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, ← ha, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h1 : (QuotientGroup.mk a : X ⧸ Subgroup.center X) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    have h3 : a ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(Subgroup.center X)) (x := ⟨a, h⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    have hdvd := orderOf_dvd_of_pow_eq_one h3
    rw [ha] at hdvd
    norm_num at hdvd
  exact orderOf_eq_prime h2 h1

end CFSG.Quasithin.H.Mathieu.M22Link
end
