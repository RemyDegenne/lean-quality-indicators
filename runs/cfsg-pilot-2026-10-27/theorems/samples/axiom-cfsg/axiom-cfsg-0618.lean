public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne

local macro "comm_group" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
             abel))

variable {V : Type} [CommGroup V]

namespace LamPair

section Coordinates

open CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule Matrix

variable {x y z : MulAut V} {u w c : V}

variable {β : V →* Multiplicative (Fin 2 → GaloisField 2 1)}

theorem coord_surjective (hV : ∀ v : V, v ^ 2 = 1) (hx : IsTransv x u) (hy : IsTransv y w)
    (hxw : x w = w * u) (hyu : y u = u * w)
    (hβ : ∀ v, Multiplicative.toAdd (β v) = ![eps x v, eps y v]) : Function.Surjective β := by
  have hxu : eps x u = 0 := eps_centre hV hx
  have hyw : eps y w = 0 := eps_centre hV hy
  have hxw1 : eps x w = 1 := eps_eq_one_of_apply hx.ne hxw
  have hyu1 : eps y u = 1 := eps_eq_one_of_apply hy.ne hyu
  intro t
  have ht : Multiplicative.toAdd t = ![Multiplicative.toAdd t 0, Multiplicative.toAdd t 1] := by
    ext i
    fin_cases i <;> rfl
  rcases gf2_eq_zero_or_one (Multiplicative.toAdd t 0) with ha | ha <;>
    rcases gf2_eq_zero_or_one (Multiplicative.toAdd t 1) with hb | hb
  · refine ⟨1, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, eps_one, eps_one]
  · refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, hxu, hyu1]
  · refine ⟨w, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, hxw1, hyw]
  · refine ⟨w * u, Multiplicative.toAdd.injective ?_⟩
    rw [hβ, ht, ha, hb, eps_mul hV hx, eps_mul hV hy, hxu, hyu1, hxw1, hyw, zero_add, add_zero]

end Coordinates
end LamPair
end CFSG.CGT.PushingUpLit.BHS
end
