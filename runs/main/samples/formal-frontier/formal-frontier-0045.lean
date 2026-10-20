@[expose] public section

open scoped Topology

namespace PadicInt

theorem inv_succ_notMem_int_span_intCast (p : ℕ) [Fact p.Prime] (a : ℤ) :
    PadicInt.inv ((p + 1 : ℕ) : ℤ_[p]) ∉ Submodule.span ℤ {(a : ℤ_[p])} := by
  intro h
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp h
  have hnorm : ‖((p + 1 : ℕ) : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr
      (Nat.coprime_self_add_right.mpr ((Nat.coprime_one_right_iff p).mpr trivial))
  have hmul : ((p + 1 : ℕ) : ℤ) * (z * a) = 1 := by
    apply (PadicInt.intCast_eq (p := p) _ 1).mp
    calc
      ((((p + 1 : ℕ) : ℤ) * (z * a) : ℤ) : ℤ_[p]) =
          ((p + 1 : ℕ) : ℤ_[p]) * (z • (a : ℤ_[p])) := by
            simp only [Int.cast_mul, Int.cast_natCast, zsmul_eq_mul]
      _ = ((p + 1 : ℕ) : ℤ_[p]) *
          PadicInt.inv ((p + 1 : ℕ) : ℤ_[p]) := by rw [hz]
      _ = ((1 : ℤ) : ℤ_[p]) := by
        simpa only [Int.cast_one] using PadicInt.mul_inv hnorm
  have hq : (1 : ℤ) < ((p + 1 : ℕ) : ℤ) :=
    Nat.one_lt_cast.mpr ((Fact.out : p.Prime).one_lt.trans_le (Nat.le_succ p))
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with hq_one | hq_neg_one
  · exact hq.ne' hq_one
  · have hbad : (1 : ℤ) < -1 := by simpa only [hq_neg_one] using hq
    exact (by decide : ¬ (1 : ℤ) < -1) hbad

end PadicInt
end
