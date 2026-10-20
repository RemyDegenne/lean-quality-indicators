@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_365_12 :
    Uω (aρ 12) (bρ 12) (47022694589997 / 128000000000000 : ℝ) ≤
      (-(640305991230515290559 / 312500000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_12]) (by norm_num [bρ_12])]; exact Lmid_12

end Zeta5Irrational
end
