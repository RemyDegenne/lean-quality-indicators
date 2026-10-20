@[expose] public section

universe u

noncomputable section

namespace ZFSet

notation "ω" => omega

namespace ZFNat

lemma right_distrib_mul_sub {n m k : ZFNat} : (m - k)*n = m*n - k*n := by
  rw [mul_comm, left_distrib_mul_sub, mul_comm, mul_comm k]

end ZFNat
end ZFSet
end
end
