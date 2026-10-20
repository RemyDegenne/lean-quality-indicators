@[expose] public section

open Real

namespace Zeta32.Fstar.B2

noncomputable section

theorem rho_pt6 : (153 / 500 : ℝ) ≤ rhoA aMinus (xk 6) :=
  rho_ge_of (sl := (2163 / 1250 : ℝ)) (sh := (173041 / 100000 : ℝ)) (U1 := (211761 / 100000 :
    ℝ)) (U5 := (266853 / 50000 : ℝ))
    (P := (131430 : ℝ)) (by norm_num [xk, aMinus]) (by norm_num [xk, aMinus]) (by norm_num) (by
      norm_num [xk, aMinus])
    (by norm_num) (by norm_num [xk, aMinus]) (by norm_num) (by norm_num [aMinus]) (by norm_num)
      (by norm_num [aMinus])
    (by norm_num) (by norm_num) (by norm_num [aMinus]) (by norm_num)
    (le_trans (by norm_num [lser]) (log_ge _ 17 (by norm_num)))

end
end Zeta32.Fstar.B2
end
