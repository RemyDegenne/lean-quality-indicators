namespace OAI

namespace GeneralizedStarHeight

universe u

universe uP uA uA2 uC uC2 uC3 uC4 uC5

universe uι uP2 uP3 uP4 uC6 uC7 uC8 uC9

universe uT uA3 uB uC10 uT2 uA4 uB2 uC11

universe uA5 uB3 uC12 uT3 uA6 uB4 uC13 uT4

universe uA7 uB5 uC14 uT5 uA8 uB6 uC15 uT6

universe uA9 uB7 uC16 uT7 uA10 uB8 uC17 uA11

universe uB9 uA12 uB10 uC18 uA13 uB11 uP5 uC19

universe uT8 uP6 uC20 uT9 uP7 uT10 uP8 uT11

universe uP9 uC21

namespace RobustClock

variable {P : Type uP} [DecidableEq P]

lemma type_one_difference {i j : Circle}
    (hi : i ∈ Near centersI (1 / 16)) (hj : j ∈ Near centersJ (1 / 16)) :
    1 / 24 ≤ ‖i - j‖ := by
  obtain ⟨c, hc, hic⟩ := hi
  obtain ⟨d, hd, hjd⟩ := hj
  have hsep := center_separation hc hd
  have ht := dist_triangle4 c i j d
  rw [dist_comm c i, dist_eq_norm i j] at ht
  linarith

end RobustClock
end GeneralizedStarHeight
end OAI
