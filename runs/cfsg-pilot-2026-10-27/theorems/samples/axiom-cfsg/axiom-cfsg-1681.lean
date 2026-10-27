public section

namespace CFSG.Quasithin.B42G2Id

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 Matrix

open CFSG.Timmesfeld.RankTwo (hexRoot hexRoot_injective)

open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

local macro "zorn_q" : tactic => `(tactic| (
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w]
  simp only [g2Act_mul_apply', g2Act_sl3P, g2Act_gW, g2Act_x0q, g2Act_x1q, g2Act_x2q,
    g2Act_y0q, g2Act_y1q, g2Act_y2q, g2Act_tv02, g2Act_tv12, g2Act_tv10, g2Act_tv20,
    g2Act_tv21, g2Act_tv01, map_one, AddMonoid.End.coe_one, id_eq] <;>
  apply q6_congr <;> ring_nf <;> reduce_mod_char!))

theorem zNeg_inv (i : Fin 6) (c : F) : (zNeg i c)⁻¹ = zNeg i c := by
  fin_cases i <;> simp only [zNeg, g2X_inv, g2Y_inv, ← map_inv, tv_inv]

end CFSG.Quasithin.B42G2Id
end
