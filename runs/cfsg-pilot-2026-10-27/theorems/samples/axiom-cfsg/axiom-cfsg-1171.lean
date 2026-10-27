public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace PData

variable (d : PData H)

include d

theorem conj_pow_odd {n : X} (hna : n * h.a = h.a * n) (hnb : n * d.b * n⁻¹ = h.a * d.b)
    (i : ℕ) : n ^ (2 * i + 1) * d.b * (n ^ (2 * i + 1))⁻¹ = h.a * d.b := by
  have hn2 : n ^ 2 * d.b * (n ^ 2)⁻¹ = d.b := by
    have h1 : n * (h.a * d.b) * n⁻¹ = d.b := by
      rw [show n * (h.a * d.b) * n⁻¹ = (n * h.a * n⁻¹) * (n * d.b * n⁻¹) by group, hnb,
        show n * h.a * n⁻¹ = h.a by rw [hna, mul_inv_cancel_right], ← mul_assoc,
        Six.a_mul_a_self h, one_mul]
    rw [pow_two, show n * n * d.b * (n * n)⁻¹ = n * (n * d.b * n⁻¹) * n⁻¹ by group, hnb, h1]
  induction i with
  | zero => simpa using hnb
  | succ i ih =>
    rw [show 2 * (i + 1) + 1 = 2 + (2 * i + 1) by ring, pow_add,
      show n ^ 2 * n ^ (2 * i + 1) * d.b * (n ^ 2 * n ^ (2 * i + 1))⁻¹ =
        n ^ 2 * (n ^ (2 * i + 1) * d.b * (n ^ (2 * i + 1))⁻¹) * (n ^ 2)⁻¹ by group, ih,
      show n ^ 2 * (h.a * d.b) * (n ^ 2)⁻¹ = (n ^ 2 * h.a * (n ^ 2)⁻¹) * (n ^ 2 * d.b * (n ^ 2)⁻¹)
        by group, hn2]
    congr 1
    have hna2 : n ^ 2 * h.a = h.a * n ^ 2 := by
      rw [pow_two, mul_assoc, hna, ← mul_assoc, hna, mul_assoc]
    rw [hna2, mul_inv_cancel_right]

end PData
end L83Hyp
end Hyp52
end CFSG.ComponentClassification.GSThmB
end
