public section

namespace CFSG.EvenSporadicStandard.M22Std.P21L52

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

section Alg

variable [Algebra (ZMod 2) K]

theorem no_order_ten_of_equiv (hK : Nat.card K = 2) {E : Type} [Group E]
    (e : E ≃* projectiveSL 5 K) (g : E) : orderOf g ≠ 10 := by
  intro hg
  let ρ : E →* Module.End (ZMod 2) (Fin 5 → K) :=
    rep.comp ((eSL hK 5).toMonoidHom.comp e.toMonoidHom)
  have hρ : Function.Injective ρ :=
    rep_injective.comp ((eSL hK 5).injective.comp e.injective)
  set y := g ^ 2 with hy
  set u := g ^ 5 with hu
  have hy5 : orderOf y = 5 := by
    rw [hy, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hu2 : orderOf u = 2 := by
    rw [hu, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy5; omega
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have hcomm : u * y = y * u := by rw [hu, hy, ← pow_add, ← pow_add, add_comm]
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have huu : u * u = 1 := by
    rw [← sq, ← hu2]; exact pow_orderOf_eq_one u
  have h1 := P21Field.eq_one_of_commute_five (le_of_eq (finrank_pi_five hK)) (ρ y) (ρ u)
    (by rw [← map_pow, hy5', map_one])
    (fun h => hy1 (hρ (by rw [h, map_one])))
    (by rw [← map_mul, huu, map_one]) (by rw [← map_mul, ← map_mul, hcomm])
  exact hu1 (hρ (by rw [h1, map_one]))

end Alg
end CFSG.EvenSporadicStandard.M22Std.P21L52
end
