@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_369_15 :
    Uω (aρ 15) (bρ 15) (47357563191033 / 128000000000000 : ℝ) ≤
      (-(268788866070650094343 / 156250000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_15]) (by norm_num [bρ_15])]; exact Lmid_15

end Zeta5Irrational
end
