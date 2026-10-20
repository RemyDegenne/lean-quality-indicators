@[expose] public section

open Finset

namespace Zeta5Irrational

lemma U_270_16 :
    Uω (aρ 16) (bρ 16) (3593013491621 / 16000000000000 : ℝ) ≤
      (-(419641552645073499393 / 250000000000000000000 : ℝ)) :=
  by rw [Uω_of_mem (by norm_num [aρ_16]) (by norm_num [bρ_16])]; exact Lmid_16

end Zeta5Irrational
end
