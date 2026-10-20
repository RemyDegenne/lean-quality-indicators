@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_362_11 :
    Uω (aρ 11) (bρ 11) (2338577156961 / 6400000000000 : ℝ) ≤
      (-(4457298065613116122159 / 2000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_11]) (by norm_num [bρ_11])]; exact Lmid_11

end Zeta5Irrational
end
