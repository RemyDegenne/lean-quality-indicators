public section

namespace CFSG.ASVolI

open CFSG.Open

section

section C0

open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A CFSG.Quasithin.H13.Ch4.B414.M

variable {F : Type} [Field F]

theorem burnsideB4h_act_fix_zpowers [Fintype F] (hF : Fintype.card F = 4) (k : ℕ)
    {x : Matrix.ProjGenLinGroup (Fin 3) F} {M : Matrix (Fin 3) (Fin 3) F}
    (h : burnsideB4h_act k x M = M) {y : Matrix.ProjGenLinGroup (Fin 3) F}
    (hy : y ∈ Subgroup.zpowers x) : burnsideB4h_act k y M = M := by
  let S : Subgroup (Matrix.ProjGenLinGroup (Fin 3) F) :=
    { carrier := {y | burnsideB4h_act k y M = M}
      one_mem' := burnsideB4h_act_one hF k M
      mul_mem' := fun {a b} ha hb => by
        show burnsideB4h_act k (a * b) M = M
        rw [burnsideB4h_act_mul hF, show burnsideB4h_act k b M = M from hb,
          show burnsideB4h_act k a M = M from ha]
      inv_mem' := fun {a} ha => by
        show burnsideB4h_act k a⁻¹ M = M
        conv_lhs => rw [← show burnsideB4h_act k a M = M from ha]
        rw [← burnsideB4h_act_mul hF, inv_mul_cancel, burnsideB4h_act_one hF] }
  exact (Subgroup.zpowers_le.2 (show x ∈ S from h)) hy

end C0
end
end CFSG.ASVolI
end
