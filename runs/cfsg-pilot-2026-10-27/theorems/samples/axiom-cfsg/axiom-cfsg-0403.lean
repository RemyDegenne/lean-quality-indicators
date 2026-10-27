public section

namespace CFSG.Quasithin.H13.L32A.M755

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 Orbit

theorem facts_yB : ∀ b ∈ [2, 4, 6],
    mmul (wMatC (yW b)) (sM b) = mmul (sM b) (wMatC (yW b)) ∧
      ∀ c ∈ lineB b, c ≠ 0 → nq (mact (wMatC (yW b)) c) ∈ lineB b ∧
        nq (mact (wMatC (yW b)) c) ≠ c := by
  decide +kernel

end CFSG.Quasithin.H13.L32A.M755
end
