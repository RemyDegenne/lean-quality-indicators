public section

namespace CFSG.Quasithin.Fan86

variable {H : Type*} [Group H]

macro "idc2 " h:term:max hR:term:max hC:term:max hww:term:max : tactic =>
  `(tactic| (simp only [($h).t_eq, ($h).zm0, ($h).zm1, ($h).zm2, ($h).za0, ($h).za1, ($h).za2,
      ($h).ym0, ($h).ym1, ($h).ym2, ($h).ub_eq, swap12_zero, swap12_one, swap12_two,
      fin3_neg_add_01, fin3_neg_add_02, fin3_neg_add_10, fin3_neg_add_12, fin3_neg_add_20,
      fin3_neg_add_21]; try collc2 $hR $hC $hww))

macro "idc0 " h:term:max hR:term:max hC:term:max : tactic =>
  `(tactic| (simp only [($h).t_eq, ($h).zm0, ($h).zm1, ($h).zm2, ($h).za0, ($h).za1, ($h).za2,
      ($h).ym0, ($h).ym1, ($h).ym2, ($h).ub_eq, swap12_zero, swap12_one, swap12_two,
      fin3_neg_add_01, fin3_neg_add_02, fin3_neg_add_10, fin3_neg_add_12, fin3_neg_add_20,
      fin3_neg_add_21]; try collc0 $hR $hC))

variable {x w za : H} {y z : Fin 5 → H} {xb t ub : H} {zm ym za' : Fin 3 → H}

namespace IdsBase

variable (h : IdsBase w za y z xb t ub zm ym za')

include h

theorem f911_conj :
    xb⁻¹ * z 0 * xb = zm 1 ∧ xb⁻¹ * ym 0 * xb = ym 1 ∧ xb⁻¹ * za * xb = za' 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [h.zm0] using h.xz 0
  · simpa using h.xy 0
  · simpa [h.za0] using h.xa 0

end IdsBase
end CFSG.Quasithin.Fan86
end
