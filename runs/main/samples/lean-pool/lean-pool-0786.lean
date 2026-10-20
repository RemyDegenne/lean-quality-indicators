@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_13_14 :
    Uω (aρ 14) (bρ 14) (283911191 / 1000000000000 : ℝ) ≤
      (-(8977612329965299982791 / 5000000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_14]) (by norm_num [bρ_14])]; exact Lmid_14

end Zeta5Irrational
end
