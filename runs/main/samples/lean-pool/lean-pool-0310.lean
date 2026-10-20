@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_63_4 :
    Uω (aρ 4) (bρ 4) (468310782911 / 16000000000000 : ℝ) ≤
      (-(11449496158609380585237 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_4]) (by norm_num [bρ_4])]; exact Lmid_4

end Zeta5Irrational
end
