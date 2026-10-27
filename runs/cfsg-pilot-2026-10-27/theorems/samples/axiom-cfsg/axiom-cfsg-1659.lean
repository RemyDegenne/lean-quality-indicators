public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag}

variable (K : Type) [Field K]

variable {K}

variable [Finite K]

theorem eq_of_xElement_mul_mul_eq {i j k : Fin τ.rank} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {a a' b b' c c' : K}
    (h : xElement i a * xElement j b * xElement k c = xElement i a' * xElement j b' * xElement k c') :
    a = a' ∧ b = b' ∧ c = c' := by
  rw [mul_assoc, mul_assoc] at h
  obtain ⟨ha, h'⟩ := eq_of_xElement_mul_eq
    (mul_mem (xElement_mem_Uplus_simple hij b) (xElement_mem_Uplus_simple hik c))
    (mul_mem (xElement_mem_Uplus_simple hij b') (xElement_mem_Uplus_simple hik c')) h
  obtain ⟨hb, hc⟩ := eq_of_xElement_mul_xElement_eq hjk h'
  exact ⟨ha, hb, hc⟩

end CFSG.LieType.Chevalley
end
