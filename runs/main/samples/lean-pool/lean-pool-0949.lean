@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_58_6 :
    Uω (aρ 6) (bρ 6) (111010421657 / 4000000000000 : ℝ) ≤
      (-(3698074464695343529243 / 1000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_6]) (by norm_num [bρ_6])]; exact Lmid_6

end Zeta5Irrational
end
