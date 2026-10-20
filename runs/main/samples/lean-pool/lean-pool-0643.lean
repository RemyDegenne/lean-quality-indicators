@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_308_13 :
    Uω (aρ 13) (bρ 13) (36730850763921 / 128000000000000 : ℝ) ≤
      (-(4762195995179309567439 / 2500000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_13]) (by norm_num [bρ_13])]; exact Lmid_13

end Zeta5Irrational
end
